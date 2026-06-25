import EqCheckingAbstractInterpretation.Ready.ConcreteTransformer

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/-!
# Denotational RS Difference via Finite Certificates

This module provides an independent denotational characterization of RS differences
using finite witness certificates. This avoids direct recursion on multi-parameter
types that triggers Lean's termination checker.

Key idea:
- `RSDenotationalCert o` is a **structural inductive datatype** indexed by RSObs `o`
  (no recursion issues—just inductive structure)
- `isValidCert` is a validation **predicate** (can be recursive, but simpler than full denotation)
- `rsDifferenceDenotational` is defined as **exists valid certificate** (no recursion)
- Equivalence to `lfpDRS` is then proven by relating valid certificates to lfp membership

This mirrors the paper's denotational definition while sidestepping Lean's termination constraints.
-/

/--
Finite certificate witnessing that an RS observation is in the concrete difference.

This is an inductive datatype (not recursive definition), indexed by the observation
it certifies. The recursion on observation structure is purely structural, so
the Lean kernel accepts it immediately.
-/
inductive RSDenotationalCert : RSObs Action → Type (u + 1) where
  | tt_cert : RSDenotationalCert .tt
  | node_cert {pos : List (Action × RSObs Action)} {neg : List Action}:
  ((i : Fin pos.length) → RSDenotationalCert (pos.get i).2) →
      RSDenotationalCert (.node pos neg)

/--
Validation predicate: check if a certificate is valid at pair (p, Q) under environment.

This is the recursive validation function (separate from the structural certificate).
It checks three conditions:
1. A cover of the right-hand states by local failure reasons: each q ∈ Q is assigned
  either to the negative tests or to some positive branch
2. For each positive branch (a, o): exists p' ∈ Der(p,a) with valid cert for o at
  (p', Der(Q_a, a)) for the states assigned to that branch
3. For each negative test b: ¬Enabled(env, p, b)
4. For each q assigned to the negative tests: some b ∈ neg is enabled at q

This recursion is over the certificate structure, which is well-founded.
-/
def isValidRSCert
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    {o : RSObs Action}
    (cert : RSDenotationalCert o) : Prop :=
  match o, cert with
  | .tt, .tt_cert =>
      -- Base case: ⊤ distinguishes p from Q iff Q is empty
      ∀ q, ¬ Q q
  | .node pos neg, .node_cert pos_certs =>
      -- Recursive case: assign each right-hand state to one local failure reason
      ∃ Qneg : ProcSet Action Name,
        ∃ Qpos : Fin pos.length → ProcSet Action Name,
      (-- 1. Positive branches exist with valid certs for their assigned states
       (∀ (i : Fin pos.length),
       ∃ p', Deriv env p (pos.get i).1 p' ∧
             isValidRSCert env p' (DerivSetOf env (Qpos i) (pos.get i).1) (pos_certs i))
      ∧
      (-- 2. All negations are disabled at p
    ∀ (b : Action) (_ : b ∈ neg), ¬ Enabled env p b)
      ∧
      (-- 3. Every q assigned to the negative side enables some refused action
    ∀ (q : CCS Action Name) (_ : Qneg q), ∃ (b : Action) (_ : b ∈ neg), Enabled env q b)
      ∧
      (-- 4. Every right-hand state is assigned to some local failure reason
    ∀ (q : CCS Action Name) (_ : Q q), Qneg q ∨ ∃ i, Qpos i q))

/--
Denotational RS difference using finite certificates:
an observation is distinguishing iff a valid certificate exists.
-/
def rsDifferenceDenotational
    (env : Env Action Name) :
    DiffSysRS Action Name (RSObs Action) :=
  fun p Q o => ∃ cert : RSDenotationalCert o, isValidRSCert env p Q cert

/--
Soundness: any valid certificate gives an element of the concrete lfp.

For any certificate of observation o that is valid at (p, Q), we show that
o is in lfpDRS env p Q by induction on the certificate structure.
The induction hypothesis ensures that at each step, the DRS conditions are met.
-/
theorem isValidCert_implies_lfp
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    {o : RSObs Action}
    (cert : RSDenotationalCert o)
    (hValid : isValidRSCert env p Q cert) :
    lfpDRS env p Q o := by
  intro ρ hρ
  have hSound :
      ∀ {o' : RSObs Action} (c : RSDenotationalCert o')
        (p' : CCS Action Name) (Q' : ProcSet Action Name),
        isValidRSCert env p' Q' c → DRS env ρ p' Q' o' := by
    intro o' c
    induction c with
    | tt_cert =>
        intro p' Q' hVal
        exact hVal
    | @node_cert pos neg pos_certs ih =>
        intro p' Q' hVal
        rcases hVal with ⟨Qneg, Qpos, h_pos, h_neg_p, h_neg_Q, h_cover⟩
        refine ⟨Qneg, Qpos, ?_⟩
        refine ⟨?_, h_neg_p, ?_, h_cover⟩
        intro i
        rcases h_pos i with ⟨pNext, hDer, hChildValid⟩
        have hChildDRS : DRS env ρ pNext (DerivSetOf env (Qpos i) (pos.get i).1) (pos.get i).2 :=
          ih i pNext (DerivSetOf env (Qpos i) (pos.get i).1) hChildValid
        exact ⟨pNext, hDer, hρ pNext (DerivSetOf env (Qpos i) (pos.get i).1) (pos.get i).2 hChildDRS⟩
        · intro q hQneg
          rcases h_neg_Q q hQneg with ⟨b, hb, hEn⟩
          exact ⟨b, hb, hEn⟩

  have hDRS : DRS env ρ p Q o := hSound cert p Q hValid
  exact hρ p Q o hDRS

/--
Completeness: any element of the concrete lfp admits a valid certificate.

For any observation in lfpDRS env p Q, we construct a valid certificate
by induction on the observation structure, extracting the certificate structure
from the DRS conditions.
-/
theorem lfp_implies_isValidCert
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (o : RSObs Action)
    (h_lfp : lfpDRS env p Q o) :
    ∃ cert : RSDenotationalCert o, isValidRSCert env p Q cert := by
  classical
  let ρ : DiffSysRS Action Name (RSObs Action) :=
    fun p' Q' o' => ∃ cert : RSDenotationalCert o', isValidRSCert env p' Q' cert

  have h_prefixpoint : ∀ p' Q' o', DRS env ρ p' Q' o' → ρ p' Q' o' := by
    intro p' Q' o' hDRS
    cases o' with
    | tt =>
        exact ⟨.tt_cert, hDRS⟩
    | node pos neg =>
        rcases hDRS with ⟨Qneg, Qpos, h_pos, h_neg_p, h_neg_Q, h_cover⟩
        have h_pos' :
            ∀ (i : Fin pos.length),
              ∃ pNext : CCS Action Name,
                ∃ cert : RSDenotationalCert (pos.get i).2,
                  Deriv env p' (pos.get i).1 pNext ∧
                  isValidRSCert env pNext (DerivSetOf env (Qpos i) (pos.get i).1) cert := by
          intro i
          rcases h_pos i with ⟨pNext, hDer, hRho⟩
          rcases hRho with ⟨cert, hCert⟩
          exact ⟨pNext, cert, hDer, hCert⟩

        let pos_certs : (i : Fin pos.length) → RSDenotationalCert (pos.get i).2 :=
          fun i => Classical.choose (Classical.choose_spec (h_pos' i))
        refine ⟨RSDenotationalCert.node_cert pos_certs, ?_⟩
        refine ⟨Qneg, Qpos, ?_⟩
        refine ⟨?_, h_neg_p, ?_, h_cover⟩
        intro i
        let pNext : CCS Action Name := Classical.choose (h_pos' i)
        have h_pair :
            Deriv env p' (pos.get i).1 pNext ∧
            isValidRSCert env pNext (DerivSetOf env (Qpos i) (pos.get i).1) (pos_certs i) := by
          dsimp [pNext, pos_certs]
          exact Classical.choose_spec (Classical.choose_spec (h_pos' i))
        exact ⟨pNext, h_pair.1, h_pair.2⟩
        · intro q hQneg
          rcases h_neg_Q q hQneg with ⟨b, hb, hEn⟩
          exact ⟨b, hb, hEn⟩

  simpa [ρ] using h_lfp ρ h_prefixpoint

/--
Main theorem: the denotational and lfp characterizations are equivalent.
-/
theorem rsDifferenceDenotational_eq_lfpDRS
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (o : RSObs Action) :
    rsDifferenceDenotational env p Q o ↔ lfpDRS env p Q o := by
  constructor
  · intro ⟨cert, hValid⟩
    exact isValidCert_implies_lfp env p Q cert hValid
  · intro h_lfp
    exact lfp_implies_isValidCert env p Q o h_lfp

end EqCheckingAbstractInterpretation.Ready
