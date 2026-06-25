import EqCheckingAbstractInterpretation.Ready.ConcreteTransformer

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/-- Pointwise order on abstract capability systems via upward-closure inclusion. -/
def AbsSysRSLe
    (ρa σa : AbsSysRS Action Name) : Prop :=
  ∀ p Q c, upClosure (ρa p Q) c → upClosure (σa p Q) c

/--
Exact concretization of a capability antichain back to RS observations.
An observation is represented whenever one abstract capability is below its
exact required capability.
-/
def gammaDRSAbs
    (ρa : AbsSysRS Action Name) :
    DiffSysRS Action Name (RSObs Action) :=
  fun p Q o => ∃ c, ρa p Q c ∧ capLe c (reqOfObs o)

/-- Exact abstract predecessor transformer on minimal capability antichains. -/
def bestDRS
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name) :
    AbsSysRS Action Name :=
  fun p Q c => alphaCap rsObsCap (DRS env (gammaDRSAbs ρa) p Q) c

/--
Raw explicit expansion of `bestDRS`: choose one-step RS observations together with
child capabilities justifying their membership in the concretization.
-/
def bestDRSRawExplicit
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name) :
    AbsSysRS Action Name :=
  fun p Q c =>
    ∃ pos : List (Action × RSObs Action),
      ∃ neg : List Action,
      ∃ Qneg : ProcSet Action Name,
        ∃ Qpos : Fin pos.length → ProcSet Action Name,
          (∀ i,
            ∃ p', Deriv env p (pos.get i).1 p' ∧
              ∃ d, ρa p' (DerivSetOf env (Qpos i) (pos.get i).1) d ∧
                capLe d (reqOfObs (pos.get i).2)) ∧
          (∀ b, b ∈ neg → ¬ Enabled env p b) ∧
          (∀ q, Qneg q → ∃ b, b ∈ neg ∧ Enabled env q b) ∧
          (∀ q, Q q → Qneg q ∨ ∃ i, Qpos i q) ∧
          capLe (reqOfObs (.node pos neg)) c

/-- Minimal-capability pruning of the explicit paper-style predecessor transformer. -/
def bestDRSExplicit
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name) :
    AbsSysRS Action Name :=
  fun p Q c => minimalCap (bestDRSRawExplicit env ρa p Q) c

/-- Pointwise equivalence between the explicit raw transformer and `alphaCapRaw`. -/
theorem bestDRSRawExplicit_spec
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability) :
    bestDRSRawExplicit env ρa p Q c ↔
      alphaCapRaw rsObsCap (DRS env (gammaDRSAbs ρa) p Q) c := by
  constructor
  · intro h
    rcases h with ⟨pos, neg, Qneg, Qpos, hPos, hNegP, hNegQ, hCover, hCap⟩
    refine ⟨.node pos neg, ?_, hCap⟩
    refine ⟨Qneg, Qpos, ?_, hNegP, hNegQ, hCover⟩
    intro i
    rcases hPos i with ⟨p', hDer, d, hd, hLe⟩
    exact ⟨p', hDer, ⟨d, hd, hLe⟩⟩
  · intro h
    rcases h with ⟨o, hDRS, hCap⟩
    cases o with
    | tt =>
        refine ⟨([] : List (Action × RSObs Action)), ([] : List Action),
          (∅ : ProcSet Action Name), (fun i => nomatch i), ?_, ?_, ?_, ?_, ?_⟩
        · intro i
          nomatch i
        · intro b hb
          cases hb
        · intro q hq
          cases hq
        · intro q hq
          exact False.elim (hDRS q hq)
        · simpa [reqOfObs, childrenReq, req] using hCap
    | node pos neg =>
        rcases hDRS with ⟨Qneg, Qpos, hPos, hNegP, hNegQ, hCover⟩
        refine ⟨pos, neg, Qneg, Qpos, ?_, hNegP, hNegQ, hCover, hCap⟩
        intro i
        rcases hPos i with ⟨p', hDer, hGamma⟩
        rcases hGamma with ⟨d, hd, hLe⟩
        exact ⟨p', hDer, d, hd, hLe⟩

/-- The explicit paper-style transformer agrees pointwise with `bestDRS`. -/
theorem bestDRSExplicit_iff
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability) :
    bestDRSExplicit env ρa p Q c ↔ bestDRS env ρa p Q c := by
  unfold bestDRSExplicit bestDRS alphaCap
  constructor
  · intro h
    refine ⟨(bestDRSRawExplicit_spec env ρa p Q c).1 h.1, ?_⟩
    intro d hd hdLe
    exact h.2 d ((bestDRSRawExplicit_spec env ρa p Q d).2 hd) hdLe
  · intro h
    refine ⟨(bestDRSRawExplicit_spec env ρa p Q c).2 h.1, ?_⟩
    intro d hd hdLe
    exact h.2 d ((bestDRSRawExplicit_spec env ρa p Q d).1 hd) hdLe

/-- The explicit paper-style transformer is definitionally equivalent to `bestDRS`. -/
theorem bestDRSExplicit_eq_bestDRS
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name) :
    bestDRSExplicit env ρa = bestDRS env ρa := by
  funext p Q c
  exact propext (bestDRSExplicit_iff env ρa p Q c)

/-- Abstract pre-fixpoints of `bestDRS` with respect to the antichain order. -/
def BestDRSPrefixpoint
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name) : Prop :=
  AbsSysRSLe (bestDRS env ρa) ρa

/-- Least abstract fixpoint of `bestDRS`, defined via intersection of upward closures. -/
def lfpBestDRS
    (env : Env Action Name) :
    AbsSysRS Action Name :=
  fun p Q c =>
    minimalCap (fun d =>
      ∀ ρa : AbsSysRS Action Name,
        BestDRSPrefixpoint env ρa → upClosure (ρa p Q) d) c

/-- Pointwise expansion of the exact abstract predecessor transformer. -/
theorem bestDRS_spec
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability) :
    bestDRS env ρa p Q c ↔ alphaCap rsObsCap (DRS env (gammaDRSAbs ρa) p Q) c :=
  Iff.rfl

/-- Canonical abstract lfp induced by concrete lfp via `alphaCapRaw`. -/
def lfpDRSAbsCanon
    (env : Env Action Name) :
    AbsSysRS Action Name :=
  fun p Q c => alphaCapRaw rsObsCap (lfpDRS env p Q) c

/-- Exact canonical abstract difference induced by the concrete lfp via `alphaCap`. -/
def lfpDRSAbsExactCanon
    (env : Env Action Name) :
    AbsSysRS Action Name :=
  fun p Q c => alphaCap rsObsCap (lfpDRS env p Q) c

/-- Pointwise specification of the canonical abstract lfp. -/
theorem lfpDRSAbsCanon_spec
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability) :
    lfpDRSAbsCanon env p Q c ↔ alphaCapRaw rsObsCap (lfpDRS env p Q) c :=
  Iff.rfl

/-- Pointwise specification of the exact canonical abstract lfp. -/
theorem lfpDRSAbsExactCanon_spec
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability) :
    lfpDRSAbsExactCanon env p Q c ↔ alphaCap rsObsCap (lfpDRS env p Q) c :=
  Iff.rfl

end EqCheckingAbstractInterpretation.Ready
