import EqCheckingAbstractInterpretation.Trace.AbstractTransformer

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/-- Concrete non-emptiness of trace difference for process-vs-set pairs. -/
def ConcreteDiffNonempty
    (ρ : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) : Prop :=
  ∃ tr, TraceDifferenceToSet ρ p Q tr

theorem DTrSharp_eq_alpha_comp_DTr_comp_gamma
    (ρ : Env Action Name)
    (ρa : CCS Action Name → ProcSet Action Name → Prop)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    DTrSharp ρ ρa p Q ↔ alphaDiffSys (DTr ρ (gammaDiffSys ρa)) p Q := by
  unfold DTrSharp alphaDiffSys alphaNonempty DTr gammaDiffSys gammaNonempty
  constructor
  · intro h
    rcases h with hBase | ⟨a, p', hDer, hNext⟩
    · exact ⟨[], hBase⟩
    · exact ⟨a :: [], ⟨p', hDer, hNext⟩⟩
  · intro ⟨tr, htr⟩
    cases tr with
    | nil => exact Or.inl htr
    | cons a tr' =>
        rcases htr with ⟨p', hDer, hNext⟩
        exact Or.inr ⟨a, p', hDer, hNext⟩


/-- `alpha` followed by `gamma` is pointwise the identity for the non-emptiness abstraction. -/
theorem alphaDiffSys_gammaDiffSys
    (ρa : AbsDiffSys Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    alphaDiffSys (gammaDiffSys ρa) p Q ↔ ρa p Q := by
  unfold alphaDiffSys gammaDiffSys alphaNonempty gammaNonempty
  constructor
  · intro h
    rcases h with ⟨tr, htr⟩
    exact htr
  · intro h
    exact ⟨[], h⟩

/--
Backward completeness (pointwise) of the non-emptiness abstraction for `DTr`:
`α ∘ DTr = DTrSharp ∘ α`.
-/
theorem backwardComplete_DTr
    (ρ : Env Action Name)
    (ρc : DiffSys Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    alphaDiffSys (DTr ρ ρc) p Q ↔ DTrSharp ρ (alphaDiffSys ρc) p Q := by
  unfold alphaDiffSys DTrSharp alphaNonempty DTr
  constructor
  · intro ⟨tr, htr⟩
    cases tr with
    | nil => exact Or.inl htr
    | cons a tr' =>
        rcases htr with ⟨p', hDer, hρc⟩
        exact Or.inr ⟨a, p', hDer, ⟨tr', hρc⟩⟩
  · intro h
    rcases h with hBase | ⟨a, p', hDer, hAbs⟩
    · exact ⟨[], hBase⟩
    · rcases hAbs with ⟨w, hw⟩
      exact ⟨a :: w, ⟨p', hDer, hw⟩⟩

theorem backwardComplete_DTr_funext
    (ρ : Env Action Name)
    (ρc : DiffSys Action Name) :
    alphaDiffSys (DTr ρ ρc) = DTrSharp ρ (alphaDiffSys ρc) := by
  funext p
  funext Q
  apply propext
  exact backwardComplete_DTr ρ ρc p Q

/--
Any abstract pre-fixpoint induces a concrete pre-fixpoint via `gamma`.
This is the bridge from abstract pre-fixpoints to concrete ones used in the
lfp-comparison chain (specifically in `alpha_lfpDTr_le_of_abstract_prefixpoint`).
-/
theorem gammaDiffSys_prefixpoint_of_abstract_prefixpoint
    (ρ : Env Action Name)
    (ρa : AbsDiffSys Action Name)
    (hρa : ∀ p Q, DTrSharp ρ ρa p Q → ρa p Q) :
    ∀ p Q tr, DTr ρ (gammaDiffSys ρa) p Q tr → gammaDiffSys ρa p Q tr := by
  intro p Q tr hTr
  unfold gammaDiffSys gammaNonempty
  have hAlpha : alphaDiffSys (DTr ρ (gammaDiffSys ρa)) p Q := ⟨tr, hTr⟩
  have hSharpAlpha : DTrSharp ρ (alphaDiffSys (gammaDiffSys ρa)) p Q :=
    (backwardComplete_DTr ρ (gammaDiffSys ρa) p Q).1 hAlpha
  have hId : alphaDiffSys (gammaDiffSys ρa) = ρa := by
    funext p'
    funext Q'
    apply propext
    exact alphaDiffSys_gammaDiffSys ρa p' Q'
  have hSharp : DTrSharp ρ ρa p Q := by
    simpa [hId] using hSharpAlpha
  exact hρa p Q hSharp

/--
`alpha` applied to the concrete lfp is a pre-fixpoint of `DTrSharp`.
This is the "converse" direction in the lfp alignment proof.
-/
theorem alpha_lfpDTr_is_prefixpoint
    (ρ : Env Action Name) :
    ∀ p Q, DTrSharp ρ (alphaDiffSys (lfpDTr ρ)) p Q → alphaDiffSys (lfpDTr ρ) p Q := by
  intro p Q h
  have hConcrete : alphaDiffSys (DTr ρ (lfpDTr ρ)) p Q :=
    (backwardComplete_DTr ρ (lfpDTr ρ) p Q).2 h
  rcases hConcrete with ⟨tr, hTr⟩
  exact ⟨tr, lfpDTr_prefixpoint ρ p Q tr hTr⟩

/--
`alpha(lfpDTr)` is below every abstract pre-fixpoint of `DTrSharp`.
Combined with `alpha_lfpDTr_is_prefixpoint`, this yields
`lfpDTrSharp_iff_alpha_lfpDTr`.
-/
theorem alpha_lfpDTr_le_of_abstract_prefixpoint
    (ρ : Env Action Name)
    (ρa : AbsDiffSys Action Name)
    (hρa : ∀ p Q, DTrSharp ρ ρa p Q → ρa p Q) :
    ∀ p Q, alphaDiffSys (lfpDTr ρ) p Q → ρa p Q := by
  intro p Q hAlpha
  rcases hAlpha with ⟨tr, hLfpTr⟩
  exact hLfpTr (gammaDiffSys ρa) (gammaDiffSys_prefixpoint_of_abstract_prefixpoint ρ ρa hρa)

/-- The abstract least fixpoint coincides pointwise with `alpha` of the concrete lfp. -/
theorem lfpDTrSharp_iff_alpha_lfpDTr
    (ρ : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    lfpDTrSharp ρ p Q ↔ alphaDiffSys (lfpDTr ρ) p Q := by
  constructor
  · intro hLfp
    exact hLfp _ (alpha_lfpDTr_is_prefixpoint ρ)
  · intro hAlpha
    exact alpha_lfpDTr_le_of_abstract_prefixpoint ρ (lfpDTrSharp ρ) (lfpDTrSharp_prefixpoint ρ) p Q hAlpha

/--
Canonical best-correct-approximation statement, pointwise at `(p,Q)`:
marker derivability (the abstract lfp result) equals
`alpha` applied to the concrete least fixpoint.
-/
theorem markerPresence_iff_alpha_lfpDTr
    (ρ : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    AbstractDiff ρ p Q ↔ alphaDiffSys (lfpDTr ρ) p Q := by
  apply lfpDTrSharp_iff_alpha_lfpDTr ρ p Q

/--
Best-abstraction view for marker analysis:
`AbstractDiff` is exact for the abstraction "is the concrete lfp non-empty?".
-/
theorem markerPresence_iff_lfpDTr_nonempty
    (ρ : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    AbstractDiff ρ p Q ↔ ∃ tr, lfpDTr ρ p Q tr := by
  simpa [alphaDiffSys, alphaNonempty] using
    (markerPresence_iff_alpha_lfpDTr ρ p Q)

/--
Main correctness characterization from the note:
marker presence is equivalent to concrete non-empty trace difference.
-/
theorem markerPresence_iff_concreteDiffNonempty
    (ρ : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    AbstractDiff ρ p Q ↔ ConcreteDiffNonempty ρ p Q := by
  constructor
  · intro hMarker
    rcases (markerPresence_iff_lfpDTr_nonempty ρ p Q).1 hMarker with ⟨tr, hLfpTr⟩
    exact ⟨tr, (traceDifferenceToSet_eq_lfpDTr ρ p Q tr).2 hLfpTr⟩
  · intro hConcrete
    rcases hConcrete with ⟨tr, hDiff⟩
    exact (markerPresence_iff_lfpDTr_nonempty ρ p Q).2
      ⟨tr, (traceDifferenceToSet_eq_lfpDTr ρ p Q tr).1 hDiff⟩

theorem markerPresence_singleton_iff_traceDifferenceNonempty
    (ρ : Env Action Name)
    (p q : CCS Action Name) :
    MarkerFailsPreorder ρ p q ↔ ∃ tr, TraceDifference ρ p q tr := by
  constructor
  · intro hMarker
    have hConcrete : ConcreteDiffNonempty ρ p {q} :=
      (markerPresence_iff_concreteDiffNonempty ρ p {q}).1 hMarker
    rcases hConcrete with ⟨tr, hDiffSet⟩
    exact ⟨tr, (traceDifferenceToSet_singleton ρ p q tr).1 hDiffSet⟩
  · intro hDiff
    rcases hDiff with ⟨tr, hDiff⟩
    have hConcrete : ConcreteDiffNonempty ρ p {q} :=
      ⟨tr, (traceDifferenceToSet_singleton ρ p q tr).2 hDiff⟩
    exact (markerPresence_iff_concreteDiffNonempty ρ p {q}).2 hConcrete

theorem tracePreorder_iff_no_marker
    (ρ : Env Action Name)
    (p q : CCS Action Name) :
    TracePreorder ρ p q ↔ ¬ MarkerFailsPreorder ρ p q := by
  constructor
  · intro hPre hMarker
    rcases (markerPresence_singleton_iff_traceDifferenceNonempty ρ p q).1 hMarker with ⟨tr, hDiff⟩
    have hNoDiff : ∀ tr', ¬ TraceDifference ρ p q tr' :=
      (tracePreorder_iff_noDifference ρ p q).1 hPre
    exact hNoDiff tr hDiff
  · intro hNoMarker
    have hNoDiff : ∀ tr, ¬ TraceDifference ρ p q tr := by
      intro tr hDiff
      have hMarker : MarkerFailsPreorder ρ p q :=
        (markerPresence_singleton_iff_traceDifferenceNonempty ρ p q).2 ⟨tr, hDiff⟩
      exact hNoMarker hMarker
    exact (tracePreorder_iff_noDifference ρ p q).2 hNoDiff

theorem traceEquivalent_iff_no_markers
    (ρ : Env Action Name)
    (p q : CCS Action Name) :
    TraceEquivalent ρ p q ↔ (¬ MarkerFailsPreorder ρ p q ∧ ¬ MarkerFailsPreorder ρ q p) := by
  constructor
  · intro hEq
    exact ⟨(tracePreorder_iff_no_marker ρ p q).1 hEq.1, (tracePreorder_iff_no_marker ρ q p).1 hEq.2⟩
  · intro h
    exact ⟨(tracePreorder_iff_no_marker ρ p q).2 h.1, (tracePreorder_iff_no_marker ρ q p).2 h.2⟩

theorem markerFails_implies_not_tracePreorder
    (ρ : Env Action Name)
    (p q : CCS Action Name) :
    MarkerFailsPreorder ρ p q → ¬ TracePreorder ρ p q := by
  intro hFail hPre
  rcases (markerPresence_singleton_iff_traceDifferenceNonempty ρ p q).1 hFail with ⟨tr, hDiff⟩
  have hNoDiff : ∀ tr', ¬ TraceDifference ρ p q tr' :=
    (tracePreorder_iff_noDifference ρ p q).1 hPre
  exact hNoDiff tr hDiff

theorem not_tracePreorder_implies_markerFails
    (ρ : Env Action Name)
    (p q : CCS Action Name) :
    ¬ TracePreorder ρ p q → MarkerFailsPreorder ρ p q := by
  intro hNotPre
  have hNotAll : ¬ ∀ tr, ¬ TraceDifference ρ p q tr := by
    intro hAll
    exact hNotPre ((tracePreorder_iff_noDifference ρ p q).2 hAll)
  have hExists : ∃ tr, TraceDifference ρ p q tr := by
    classical
    exact Classical.byContradiction (fun hNo =>
      hNotAll (fun tr hDiff => hNo ⟨tr, hDiff⟩))
  exact (markerPresence_singleton_iff_traceDifferenceNonempty ρ p q).2 hExists

theorem markerFails_iff_not_tracePreorder
    (ρ : Env Action Name)
    (p q : CCS Action Name) :
    MarkerFailsPreorder ρ p q ↔ ¬ TracePreorder ρ p q := by
  constructor
  · exact markerFails_implies_not_tracePreorder ρ p q
  · exact not_tracePreorder_implies_markerFails ρ p q

end EqCheckingAbstractInterpretation.Trace
