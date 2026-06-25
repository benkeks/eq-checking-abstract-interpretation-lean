import EqCheckingAbstractInterpretation.Ready.Basic

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/-- Pointwise order on RS difference systems. -/
def DiffSysRSLe
    (ρ σ : DiffSysRS Action Name (RSObs Action)) : Prop :=
  ∀ p Q o, ρ p Q o → σ p Q o

/--
Concrete predecessor transformer for ready-style observations.
This mirrors the paper's RS predecessor intuition at the concrete level.
-/
def DRS
    (env : Env Action Name)
    (ρ : DiffSysRS Action Name (RSObs Action))
    (p : CCS Action Name)
    (Q : ProcSet Action Name) : RSObs Action → Prop
  | .tt => ∀ q, ¬ Q q
  | .node pos neg =>
      ∃ Qneg : ProcSet Action Name,
        ∃ Qpos : Fin pos.length → ProcSet Action Name,
          (∀ i,
            ∃ p', Deriv env p (pos.get i).1 p' ∧
              ρ p' (DerivSetOf env (Qpos i) (pos.get i).1) (pos.get i).2) ∧
          (∀ b, b ∈ neg → ¬ Enabled env p b) ∧
          (∀ q, Qneg q → ∃ b, b ∈ neg ∧ Enabled env q b) ∧
          (∀ q, Q q → Qneg q ∨ ∃ i, Qpos i q)

/-- `DRS` is monotone in the difference-system argument. -/
theorem dRS_mono
    (env : Env Action Name)
    {ρ σ : DiffSysRS Action Name (RSObs Action)}
    (hLe : DiffSysRSLe ρ σ)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    ∀ o, DRS env ρ p Q o → DRS env σ p Q o := by
  intro o h
  cases o with
  | tt => exact h
  | node pos neg =>
      rcases h with ⟨Qneg, Qpos, hPos, hNegP, hNegQ, hCover⟩
      refine ⟨Qneg, Qpos, ?_, hNegP, hNegQ, hCover⟩
      intro i
      rcases hPos i with ⟨p', hDer, hRho⟩
      exact ⟨p', hDer, hLe p' (DerivSetOf env (Qpos i) (pos.get i).1) (pos.get i).2 hRho⟩

/-- Least fixpoint of `DRS`, defined as intersection of all pre-fixpoints. -/
def lfpDRS
    (env : Env Action Name) :
    DiffSysRS Action Name (RSObs Action) :=
  fun p Q o =>
    ∀ ρ : DiffSysRS Action Name (RSObs Action),
      (∀ p' Q' o', DRS env ρ p' Q' o' → ρ p' Q' o') →
      ρ p Q o

/-- `lfpDRS` is a pre-fixpoint of `DRS`. -/
theorem lfpDRS_prefixpoint
    (env : Env Action Name) :
    ∀ p Q o, DRS env (lfpDRS env) p Q o → lfpDRS env p Q o := by
  intro p Q o h ρ hρ
  cases o with
  | tt =>
      exact hρ p Q .tt h
  | node pos neg =>
      rcases h with ⟨Qneg, Qpos, hPos, hNegP, hNegQ, hCover⟩
      apply hρ
      refine ⟨Qneg, Qpos, ?_, hNegP, hNegQ, hCover⟩
      intro i
      rcases hPos i with ⟨p', hDer, hLfp⟩
      exact ⟨p', hDer, hLfp ρ hρ⟩


/--
`αcap(lfpDRS)` is itself a pre-fixpoint: one DRS step stays within `αcap(lfpDRS)`.
This is the RS analogue of `alpha_lfpDTr_is_prefixpoint`.
-/
theorem alpha_lfpDRS_is_prefixpoint
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability)
    (h : alphaCapRaw rsObsCap (DRS env (lfpDRS env) p Q) c) :
    alphaCapRaw rsObsCap (lfpDRS env p Q) c := by
  rcases h with ⟨o, hDRS, hCap⟩
  exact ⟨o, lfpDRS_prefixpoint env p Q o hDRS, hCap⟩

/--
`αcap(lfpDRS(p,Q))` is below every abstract pre-fixpoint of `DRS`.
Combined with `alpha_lfpDRS_is_prefixpoint`, this yields `lfpDRSAbsCanon_spec`.
This is the RS analogue of `alpha_lfpDTr_le_of_abstract_prefixpoint`.
-/
theorem alpha_lfpDRS_le_of_abstract_prefixpoint
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name)
    (hρa : ∀ p' Q' c', alphaCapRaw rsObsCap (lfpDRS env p' Q') c' → ρa p' Q' c')
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability)
    (hAlpha : alphaCapRaw rsObsCap (lfpDRS env p Q) c) :
    ρa p Q c :=
  hρa p Q c hAlpha

end EqCheckingAbstractInterpretation.Ready
