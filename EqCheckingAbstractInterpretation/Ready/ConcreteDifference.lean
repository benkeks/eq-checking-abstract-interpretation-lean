import EqCheckingAbstractInterpretation.Ready.ConcreteTransformer

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/-- A single process satisfies a ready-simulation observation. -/
inductive RSSem (env : Env Action Name) : CCS Action Name → RSObs Action → Prop where
  | tt (p : CCS Action Name) : RSSem env p .tt
  | node (p : CCS Action Name) (pos : List (Action × RSObs Action)) (neg : List Action)
      (next : Fin pos.length → CCS Action Name)
      (hDer : ∀ i, Deriv env p (pos.get i).1 (next i))
      (hNeg : ∀ b, b ∈ neg → ¬ Enabled env p b)
      (hPos : ∀ i, RSSem env (next i) (pos.get i).2) :
      RSSem env p (.node pos neg)

/-- Difference of independent single-process ready-simulation denotations. -/
def RSDifferenceToSet
    (env : Env Action Name) :
    DiffSysRS Action Name (RSObs Action) :=
  fun p Q o => RSSem env p o ∧ ∀ q, Q q → ¬ RSSem env q o

/-- A concrete predecessor step preserves the difference of single-process denotations. -/
private theorem dRS_sem_prefixpoint (env : Env Action Name) :
    ∀ p Q o, DRS env (RSDifferenceToSet env) p Q o → RSDifferenceToSet env p Q o := by
  classical
  intro p Q o hStep
  cases o with
  | tt =>
      exact ⟨RSSem.tt p, fun q hQ _ => hStep q hQ⟩
  | node pos neg =>
      rcases hStep with ⟨Qneg, Qpos, hPos, hNegP, hNegQ, hCover⟩
      let next : Fin pos.length → CCS Action Name := fun i => Classical.choose (hPos i)
      have hNext (i : Fin pos.length) :
          Deriv env p (pos.get i).1 (next i) ∧
            RSDifferenceToSet env (next i)
              (DerivSetOf env (Qpos i) (pos.get i).1) (pos.get i).2 := by
        exact Classical.choose_spec (hPos i)
      refine ⟨RSSem.node p pos neg next (fun i => (hNext i).1) hNegP
        (fun i => (hNext i).2.1), ?_⟩
      intro q hQ hSem
      cases hSem with
      | node _ _ _ qNext hDerQ hNegAtQ hPosQ =>
          rcases hCover q hQ with hN | ⟨i, hP⟩
          · rcases hNegQ q hN with ⟨b, hb, hEnabled⟩
            exact (hNegAtQ b hb) hEnabled
          · exact (hNext i).2.2 (qNext i) ⟨q, hP, hDerQ i⟩ (hPosQ i)

/-- Independent denotational difference equals the concrete least fixpoint. -/
theorem rsDifferenceToSet_eq_lfpDRS
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (o : RSObs Action) :
    RSDifferenceToSet env p Q o ↔ lfpDRS env p Q o := by
  classical
  constructor
  · rintro ⟨hSem, hAbsent⟩
    induction hSem generalizing Q with
    | tt p =>
        apply lfpDRS_prefixpoint env
        exact fun q hQ => hAbsent q hQ (RSSem.tt q)
    | node p pos neg next hDer hNeg hPos ih =>
        apply lfpDRS_prefixpoint env
        let Qneg : ProcSet Action Name := fun q => ∃ b, b ∈ neg ∧ Enabled env q b
        let Qpos : Fin pos.length → ProcSet Action Name :=
          fun i q => ∀ successor, Deriv env q (pos.get i).1 successor →
            ¬ RSSem env successor (pos.get i).2
        refine ⟨Qneg, Qpos, ?_, hNeg, (fun _ h => h), ?_⟩
        · intro i
          refine ⟨next i, hDer i, ih i (DerivSetOf env (Qpos i) (pos.get i).1) ?_⟩
          intro successor hSuccessor hChild
          rcases hSuccessor with ⟨q, hQpos, hDeriv⟩
          exact hQpos successor hDeriv hChild
        · intro q hQ
          by_cases hN : Qneg q
          · exact Or.inl hN
          · by_cases hP : ∃ i, Qpos i q
            · exact Or.inr hP
            · exfalso
              have hBranches (i : Fin pos.length) :
                  ∃ successor, Deriv env q (pos.get i).1 successor ∧
                    RSSem env successor (pos.get i).2 := by
                by_cases hFound : ∃ successor, Deriv env q (pos.get i).1 successor ∧
                    RSSem env successor (pos.get i).2
                · exact hFound
                · exfalso
                  apply hP
                  exact ⟨i, fun successor hDeriv hChild =>
                    hFound ⟨successor, hDeriv, hChild⟩⟩
              let qNext : Fin pos.length → CCS Action Name :=
                fun i => Classical.choose (hBranches i)
              apply hAbsent q hQ
              exact RSSem.node q pos neg qNext
                (fun i => (Classical.choose_spec (hBranches i)).1)
                (by intro b hb hEnabled; exact hN ⟨b, hb, hEnabled⟩)
                (fun i => (Classical.choose_spec (hBranches i)).2)
  · intro hLfp
    exact hLfp (RSDifferenceToSet env) (dRS_sem_prefixpoint env)

/-- Witness-preorder induced by RS difference lfp emptiness. -/
def RSWitnessPreorder
    (env : Env Action Name)
    (p q : CCS Action Name) : Prop :=
  ¬ ∃ o : RSObs Action, lfpDRS env p {q} o

/-- Witness preorder restricted to observations expressible at a capability threshold. -/
def RSWitnessPreorderAt
    (env : Env Action Name)
    (N : Capability)
    (p q : CCS Action Name) : Prop :=
  ¬ notPreorderAt rsObsCap (lfpDRS env) N p {q}

/-- Corollary: witness-preorder equals emptiness of concrete RS difference. -/
theorem rsWitnessPreorder_iff_rsDiffEmpty
    (env : Env Action Name)
    (p q : CCS Action Name) :
    RSWitnessPreorder env p q ↔
      ¬ ∃ o : RSObs Action, RSDifferenceToSet env p {q} o := by
  unfold RSWitnessPreorder
  exact not_congr (exists_congr (fun o => (rsDifferenceToSet_eq_lfpDRS env p {q} o).symm))

end EqCheckingAbstractInterpretation.Ready
