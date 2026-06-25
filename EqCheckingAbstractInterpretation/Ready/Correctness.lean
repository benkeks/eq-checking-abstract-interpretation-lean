import EqCheckingAbstractInterpretation.Ready.AbstractTransformer
import EqCheckingAbstractInterpretation.Ready.ConcreteDifference

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/--
Any observation admitted by the exact concretization of an exact capability
abstraction has a concrete witness whose required capability is no larger.
-/
theorem concrete_of_gammaDRSAbsExact
    (ρ : DiffSysRS Action Name (RSObs Action))
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (o : RSObs Action)
    (hGamma : gammaDRSAbs (fun p Q c => alphaCap rsObsCap (ρ p Q) c) p Q o) :
    ∃ o', ρ p Q o' ∧ capLe (reqOfObs o') (reqOfObs o) := by
  rcases hGamma with ⟨c, hc, hLe⟩
  have hUp : upClosure (alphaCap rsObsCap (ρ p Q)) c :=
    ⟨c, hc, capLe_refl _⟩
  have hRaw : alphaCapRaw rsObsCap (ρ p Q) c := by
    exact (upClosure_alphaCap_iff_alphaCapRaw
      rsObsCap rsObsCapMonotone (ρ p Q) c).1 hUp
  rcases hRaw with ⟨o', hRho, hCap⟩
  exact ⟨o', hRho, capLe_trans hCap hLe⟩

/--
One `DRS` step over the exact concretization of an exact capability abstraction
can be rebuilt as a concrete `DRS` step, possibly with smaller child
observations at each positive branch occurrence.
-/
theorem concrete_of_DRS_gammaDRSAbsExact
    (env : Env Action Name)
    (ρ : DiffSysRS Action Name (RSObs Action))
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (o : RSObs Action)
    (hDRS : DRS env (gammaDRSAbs (fun p Q c => alphaCap rsObsCap (ρ p Q) c)) p Q o) :
    ∃ o', DRS env ρ p Q o' ∧ capLe (reqOfObs o') (reqOfObs o) := by
  classical
  cases o with
  | tt =>
      exact ⟨.tt, hDRS, capLe_refl _⟩
  | node pos neg =>
      rcases hDRS with ⟨Qneg, Qpos, hPos, hNegP, hNegQ, hCover⟩
      have hChild :
          ∀ i : Fin pos.length,
            ∃ p' o',
              Deriv env p (pos.get i).1 p' ∧
              ρ p' (DerivSetOf env (Qpos i) (pos.get i).1) o' ∧
              capLe (reqOfObs o') (reqOfObs (pos.get i).2) := by
        intro i
        rcases hPos i with ⟨p', hDer, hGamma⟩
        rcases concrete_of_gammaDRSAbsExact
          (ρ := ρ) p' (DerivSetOf env (Qpos i) (pos.get i).1) (pos.get i).2 hGamma with
          ⟨o', hRho, hLe⟩
        exact ⟨p', o', hDer, hRho, hLe⟩
      let p' : Fin pos.length → CCS Action Name :=
        fun i => Classical.choose (hChild i)
      have hp' :
          ∀ i : Fin pos.length,
            ∃ o',
              Deriv env p (pos.get i).1 (p' i) ∧
              ρ (p' i) (DerivSetOf env (Qpos i) (pos.get i).1) o' ∧
              capLe (reqOfObs o') (reqOfObs (pos.get i).2) := by
        intro i
        exact Classical.choose_spec (hChild i)
      let childObs : Fin pos.length → RSObs Action :=
        fun i => Classical.choose (hp' i)
      have hChildSpec :
          ∀ i : Fin pos.length,
            Deriv env p (pos.get i).1 (p' i) ∧
            ρ (p' i) (DerivSetOf env (Qpos i) (pos.get i).1) (childObs i) ∧
            capLe (reqOfObs (childObs i)) (reqOfObs (pos.get i).2) := by
        intro i
        exact Classical.choose_spec (hp' i)
      let Qpos' : Fin (replaceChildren pos childObs).length → ProcSet Action Name :=
        fun i => Qpos ⟨i.1, by simpa [replaceChildren_length] using i.2⟩
      refine ⟨.node (replaceChildren pos childObs) neg, ?_, ?_⟩
      · refine ⟨Qneg, Qpos', ?_, hNegP, hNegQ, ?_⟩
        · rintro ⟨n, hn⟩
          change ∃ p',
            Deriv env p ((replaceChildren pos childObs).get ⟨n, hn⟩).1 p' ∧
              ρ p'
                (DerivSetOf env (Qpos' ⟨n, hn⟩) ((replaceChildren pos childObs).get ⟨n, hn⟩).1)
                ((replaceChildren pos childObs).get ⟨n, hn⟩).2
          let i' : Fin pos.length := ⟨n, by simpa [replaceChildren_length] using hn⟩
          have hget : (replaceChildren pos childObs).get ⟨n, hn⟩ = ((pos.get i').1, childObs i') := by
            simpa [i'] using replaceChildren_get pos childObs i'
          have hfst : ((replaceChildren pos childObs).get ⟨n, hn⟩).1 = (pos.get i').1 := by
            exact congrArg (fun ao => ao.1) hget
          have hsnd : ((replaceChildren pos childObs).get ⟨n, hn⟩).2 = childObs i' := by
            exact congrArg (fun ao => ao.2) hget
          refine ⟨p' i', ?_, ?_⟩
          · rw [hfst]
            exact (hChildSpec i').1
          · rw [hfst, hsnd]
            simpa [Qpos', i'] using (hChildSpec i').2.1
        · intro q hq
          rcases hCover q hq with hqneg | ⟨i, hi⟩
          · exact Or.inl hqneg
          · exact Or.inr ⟨⟨i.1, by simp [replaceChildren_length]⟩, hi⟩
      · exact reqOfObs_node_replaceChildren_le pos neg childObs (fun i => (hChildSpec i).2.2)

/--
Backward completeness (pointwise) of the capability abstraction for `bestDRS`:
`αcap ∘ DRS = bestDRS ∘ αcap`.
-/
theorem backwardComplete_bestDRS
    (env : Env Action Name)
    (ρ : DiffSysRS Action Name (RSObs Action))
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability) :
    alphaCap rsObsCap (DRS env ρ p Q) c ↔
      bestDRS env (fun p' Q' c' => alphaCap rsObsCap (ρ p' Q') c') p Q c := by
  have hRaw :
      ∀ d : Capability,
        alphaCapRaw rsObsCap (DRS env ρ p Q) d ↔
          alphaCapRaw rsObsCap
            (DRS env (gammaDRSAbs (fun p' Q' c' => alphaCap rsObsCap (ρ p' Q') c')) p Q) d := by
    intro d
    constructor
    · intro h
      rcases h with ⟨o, hDRS, hCap⟩
      have hDRSGamma :
          DRS env (gammaDRSAbs (fun p' Q' c' => alphaCap rsObsCap (ρ p' Q') c')) p Q o := by
        cases o with
        | tt =>
            exact hDRS
        | node pos neg =>
            rcases hDRS with ⟨Qneg, Qpos, hPos, hNegP, hNegQ, hCover⟩
            refine ⟨Qneg, Qpos, ?_, hNegP, hNegQ, hCover⟩
            intro i
            rcases hPos i with ⟨p', hDer, hρ⟩
            have hUp :
                upClosure (alphaCap rsObsCap (ρ p' (DerivSetOf env (Qpos i) (pos.get i).1)))
                  (reqOfObs (pos.get i).2) := by
              exact (upClosure_alphaCap_iff_alphaCapRaw
                rsObsCap rsObsCapMonotone
                (ρ p' (DerivSetOf env (Qpos i) (pos.get i).1))
                (reqOfObs (pos.get i).2)).2
                ⟨(pos.get i).2, hρ, capLe_refl _⟩
            rcases hUp with ⟨d', hd, hdLe⟩
            exact ⟨p', hDer, ⟨d', hd, hdLe⟩⟩
      exact ⟨o, hDRSGamma, hCap⟩
    · intro h
      rcases h with ⟨o, hDRS, hCap⟩
      rcases concrete_of_DRS_gammaDRSAbsExact env ρ p Q o hDRS with ⟨o', hConcrete, hLe⟩
      exact ⟨o', hConcrete, capLe_trans hLe hCap⟩
  unfold bestDRS alphaCap
  constructor
  · intro h
    refine ⟨(hRaw c).mp h.1, ?_⟩
    intro d hd hdLe
    exact h.2 d ((hRaw d).mpr hd) hdLe
  · intro h
    refine ⟨(hRaw c).mpr h.1, ?_⟩
    intro d hd hdLe
    exact h.2 d ((hRaw d).mp hd) hdLe

/-- Function-extensional form of `backwardComplete_bestDRS`. -/
theorem backwardComplete_bestDRS_funext
    (env : Env Action Name)
    (ρ : DiffSysRS Action Name (RSObs Action)) :
    (fun p Q c => alphaCap rsObsCap (DRS env ρ p Q) c) =
      bestDRS env (fun p' Q' c' => alphaCap rsObsCap (ρ p' Q') c') := by
  funext p Q c
  exact propext (backwardComplete_bestDRS env ρ p Q c)

/-- Any abstract pre-fixpoint induces a concrete pre-fixpoint via `gammaDRSAbs`. -/
theorem gammaDRSAbs_prefixpoint_of_abstract_prefixpoint
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name)
    (hρa : BestDRSPrefixpoint env ρa) :
    ∀ p Q o, DRS env (gammaDRSAbs ρa) p Q o → gammaDRSAbs ρa p Q o := by
  intro p Q o hDRS
  have hUpBest : upClosure (bestDRS env ρa p Q) (reqOfObs o) := by
    exact (upClosure_alphaCap_iff_alphaCapRaw
      rsObsCap rsObsCapMonotone (DRS env (gammaDRSAbs ρa) p Q) (reqOfObs o)).2
      ⟨o, hDRS, capLe_refl _⟩
  exact hρa p Q (reqOfObs o) hUpBest

/--
Any observation admitted by the exact concretization of the canonical abstract
lfp has a concrete `lfpDRS` witness whose required capability is no larger.
-/
theorem concrete_of_gammaDRSAbsExactCanon
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (o : RSObs Action)
    (hGamma : gammaDRSAbs (fun p Q c => alphaCap rsObsCap (lfpDRS env p Q) c) p Q o) :
    ∃ o', lfpDRS env p Q o' ∧ capLe (reqOfObs o') (reqOfObs o) := by
  exact concrete_of_gammaDRSAbsExact (ρ := lfpDRS env) p Q o hGamma

/--
One `DRS` step over the exact concretization of the canonical abstract lfp can
be rebuilt as a concrete `DRS` step over `lfpDRS`, possibly with smaller child
observations at each positive branch occurrence.
-/
theorem concrete_of_DRS_gammaDRSAbsExactCanon
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (o : RSObs Action)
    (hDRS : DRS env (gammaDRSAbs (fun p Q c => alphaCap rsObsCap (lfpDRS env p Q) c)) p Q o) :
    ∃ o', DRS env (lfpDRS env) p Q o' ∧ capLe (reqOfObs o') (reqOfObs o) := by
  exact concrete_of_DRS_gammaDRSAbsExact env (ρ := lfpDRS env) p Q o hDRS

/-- `lfpBestDRS` lies below every abstract pre-fixpoint of `bestDRS`. -/
theorem lfpBestDRS_le_of_abstract_prefixpoint
    (env : Env Action Name)
    (ρa : AbsSysRS Action Name)
    (hρa : BestDRSPrefixpoint env ρa)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability)
    (hLfp : lfpBestDRS env p Q c) :
    upClosure (ρa p Q) c := by
  exact minimalCap_left _ hLfp ρa hρa

/-- The exact canonical abstraction induced by `lfpDRS` is a pre-fixpoint of `bestDRS`. -/
theorem lfpDRSAbsExactCanon_prefixpoint
    (env : Env Action Name) :
    BestDRSPrefixpoint env (lfpDRSAbsExactCanon env) := by
  intro p Q c hBest
  have hRawBest : alphaCapRaw rsObsCap (DRS env (gammaDRSAbs (lfpDRSAbsExactCanon env)) p Q) c := by
    exact (upClosure_alphaCap_iff_alphaCapRaw
      rsObsCap rsObsCapMonotone (DRS env (gammaDRSAbs (lfpDRSAbsExactCanon env)) p Q) c).1 hBest
  rcases hRawBest with ⟨o, hDRS, hCap⟩
  rcases concrete_of_DRS_gammaDRSAbsExactCanon env p Q o hDRS with ⟨o', hConcrete, hLe⟩
  have hLfp : lfpDRS env p Q o' := lfpDRS_prefixpoint env p Q o' hConcrete
  have hUp : upClosure (lfpDRSAbsExactCanon env p Q) c := by
    exact (upClosure_alphaCap_iff_alphaCapRaw
      rsObsCap rsObsCapMonotone (lfpDRS env p Q) c).2 ⟨o', hLfp, capLe_trans hLe hCap⟩
  simpa [lfpDRSAbsExactCanon] using hUp

theorem below_all_abstract_prefixpoints_iff_alphaCapRaw_lfpDRS
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (c : Capability) :
    (∀ ρa : AbsSysRS Action Name,
        BestDRSPrefixpoint env ρa → upClosure (ρa p Q) c) ↔
      alphaCapRaw rsObsCap (lfpDRS env p Q) c := by
  constructor
  · intro hAll
    have hUp : upClosure (lfpDRSAbsExactCanon env p Q) c :=
      hAll (lfpDRSAbsExactCanon env) (lfpDRSAbsExactCanon_prefixpoint env)
    exact (upClosure_alphaCap_iff_alphaCapRaw
      rsObsCap rsObsCapMonotone (lfpDRS env p Q) c).1
      (by simpa [lfpDRSAbsExactCanon] using hUp)
  · intro hRaw ρa hρa
    rcases hRaw with ⟨o, hLfpObs, hCap⟩
    have hGamma : gammaDRSAbs ρa p Q o := by
      exact hLfpObs (gammaDRSAbs ρa)
        (gammaDRSAbs_prefixpoint_of_abstract_prefixpoint env ρa hρa)
    rcases hGamma with ⟨d, hd, hdLe⟩
    exact ⟨d, hd, capLe_trans hdLe hCap⟩

/-- The abstract lfp of `bestDRS` coincides with the canonical exact abstraction of `lfpDRS`. -/
theorem lfpBestDRS_eq_lfpDRSAbsExactCanon
    (env : Env Action Name) :
    lfpBestDRS env = lfpDRSAbsExactCanon env := by
  funext p Q c
  apply propext
  apply Iff.intro
  · intro hLfp
    refine ⟨?_, ?_⟩
    · exact (below_all_abstract_prefixpoints_iff_alphaCapRaw_lfpDRS env p Q c).1
        (minimalCap_left _ hLfp)
    · intro d hd hdLe
      exact hLfp.2 d
        ((below_all_abstract_prefixpoints_iff_alphaCapRaw_lfpDRS env p Q d).2 hd) hdLe
  · intro hCanon
    refine ⟨?_, ?_⟩
    · exact (below_all_abstract_prefixpoints_iff_alphaCapRaw_lfpDRS env p Q c).2 hCanon.1
    · intro d hd hdLe
      exact hCanon.2 d
        ((below_all_abstract_prefixpoints_iff_alphaCapRaw_lfpDRS env p Q d).1 hd) hdLe

--/ ============================================================================
--/ CONCRETE OBSERVATIONS: Connection to RSObs
--/ ============================================================================

/--
Concrete instantiation of the unified lfp-level threshold theorem
for the observation syntax `RSObs`.
-/
theorem abstractFailsAt_iff_notPreorderAt_rsObs_of_lfp
    (lfpConcrete : DiffSysRS Action Name (RSObs Action))
    (lfpAbs : AbsSysRS Action Name)
    (hLfp : ∀ p Q c, lfpAbs p Q c ↔ alphaCapRaw rsObsCap (lfpConcrete p Q) c)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt lfpAbs N p Q ↔ notPreorderAt rsObsCap lfpConcrete N p Q := by
  exact abstractFailsAt_iff_notPreorderAt_of_lfp
    (ObsCap := rsObsCap)
    rsObsCapMonotone
    lfpConcrete
    lfpAbs
    hLfp
    N p Q

/--
Assumption-free canonical variant: instantiate the abstract side directly as
`alphaCapRaw` applied to the concrete lfp.
-/
theorem abstractFailsAt_iff_notPreorderAt_rsObs_of_lfpCanon
    (env : Env Action Name)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt (lfpDRSAbsCanon env) N p Q ↔
      notPreorderAt rsObsCap (lfpDRS env) N p Q := by
  exact abstractFailsAt_iff_notPreorderAt_rsObs_of_lfp
    (lfpConcrete := lfpDRS env)
    (lfpAbs := lfpDRSAbsCanon env)
    (hLfp := lfpDRSAbsCanon_spec env)
    N p Q

/-- Exact-pruned canonical variant: instantiate the abstract side as `alphaCap`. -/
theorem abstractFailsAt_iff_notPreorderAt_rsObs_of_lfpExactCanon
    (env : Env Action Name)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt (lfpDRSAbsExactCanon env) N p Q ↔
      notPreorderAt rsObsCap (lfpDRS env) N p Q := by
  exact abstractFailsAt_iff_notPreorderAt_of_lfpExact
    (ObsCap := rsObsCap)
    rsObsCapMonotone
    (lfpConcrete := lfpDRS env)
    (lfpAbs := lfpDRSAbsExactCanon env)
    (hLfp := lfpDRSAbsExactCanon_spec env)
    N p Q

/--
Concrete threshold exactness stated directly over `RSDifferenceToSet`.
-/
theorem abstractFailsAt_iff_rsDifferenceThreshold
    (env : Env Action Name)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt (lfpDRSAbsCanon env) N p Q ↔
      ∃ o : RSObs Action, RSDifferenceToSet env p Q o ∧ rsObsCap N o := by
  constructor
  · intro hAbs
    rcases (abstractFailsAt_iff_notPreorderAt_rsObs_of_lfpCanon
      (Action := Action) (Name := Name) env N p Q).1 hAbs with ⟨o, hLfp, hCap⟩
    exact ⟨o, (rsDifferenceToSet_eq_lfpDRS env p Q o).2 hLfp, hCap⟩
  · intro hDiff
    rcases hDiff with ⟨o, hDiff, hCap⟩
    refine (abstractFailsAt_iff_notPreorderAt_rsObs_of_lfpCanon
      (Action := Action) (Name := Name) env N p Q).2 ?_
    exact ⟨o, (rsDifferenceToSet_eq_lfpDRS env p Q o).1 hDiff, hCap⟩

/-- Exact-pruned threshold exactness stated directly over `RSDifferenceToSet`. -/
theorem abstractFailsAtExact_iff_rsDifferenceThreshold
    (env : Env Action Name)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt (lfpDRSAbsExactCanon env) N p Q ↔
      ∃ o : RSObs Action, RSDifferenceToSet env p Q o ∧ rsObsCap N o := by
  constructor
  · intro hAbs
    rcases (abstractFailsAt_iff_notPreorderAt_rsObs_of_lfpExactCanon
      (Action := Action) (Name := Name) env N p Q).1 hAbs with ⟨o, hLfp, hCap⟩
    exact ⟨o, (rsDifferenceToSet_eq_lfpDRS env p Q o).2 hLfp, hCap⟩
  · intro hDiff
    rcases hDiff with ⟨o, hDiff, hCap⟩
    refine (abstractFailsAt_iff_notPreorderAt_rsObs_of_lfpExactCanon
      (Action := Action) (Name := Name) env N p Q).2 ?_
    exact ⟨o, (rsDifferenceToSet_eq_lfpDRS env p Q o).1 hDiff, hCap⟩

/-- Exact-pruned threshold theorem stated over the abstract lfp `lfpBestDRS`. -/
theorem abstractFailsAt_lfpBestDRS_iff_rsDifferenceThreshold
    (env : Env Action Name)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt (lfpBestDRS env) N p Q ↔
      ∃ o : RSObs Action, RSDifferenceToSet env p Q o ∧ rsObsCap N o := by
  have hEq := lfpBestDRS_eq_lfpDRSAbsExactCanon (Action := Action) (Name := Name) env
  simpa [hEq] using abstractFailsAtExact_iff_rsDifferenceThreshold
    (Action := Action) (Name := Name) env N p Q

/-- Paper-style threshold exactness for the abstract lfp `lfpBestDRS`. -/
theorem thresholdWitness_lfpBestDRS_iff_rsDifferenceThreshold
    (env : Env Action Name)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    (∃ c, lfpBestDRS env p Q c ∧ capLe c N) ↔
      ∃ o : RSObs Action, RSDifferenceToSet env p Q o ∧ rsObsCap N o := by
  simpa [abstractFailsAt, thresholdWitness] using
    abstractFailsAt_lfpBestDRS_iff_rsDifferenceThreshold
      (Action := Action) (Name := Name) env N p Q

end EqCheckingAbstractInterpretation.Ready
