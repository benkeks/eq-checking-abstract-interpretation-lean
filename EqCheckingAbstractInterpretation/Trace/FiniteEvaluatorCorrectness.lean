import EqCheckingAbstractInterpretation.FiniteEvaluator.Correctness
import EqCheckingAbstractInterpretation.Trace.FiniteEvaluator
import EqCheckingAbstractInterpretation.Trace.AbstractTransformer

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.FiniteEvaluator

universe u v w

namespace FiniteLTS

variable {Action : Type u} {State : Type v}
  [DecidableEq Action] [DecidableEq State]

/-- Boolean marker-table membership reflects ordinary list membership. -/
theorem configMem_iff (config : Config State) (marked : MarkerTable State) :
    configMem config marked = true ↔ config ∈ marked := by
  induction marked with
  | nil => simp [configMem]
  | cons entry marked ih =>
      simp only [configMem, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, ih]
      constructor
      · rintro (hEqual | hMember)
        · exact Or.inl (Prod.ext hEqual.1 hEqual.2)
        · exact Or.inr hMember
      · rintro (rfl | hMember)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr hMember

/-- Membership in a shifted competitor set comes from one competitor transition row. -/
theorem mem_shift_iff (lts : CCS.FiniteLTS Action State) (competitors : StateSet State)
    (action : Action) (target : State) :
    target ∈ shift lts competitors action ↔
      ∃ competitor ∈ competitors, target ∈ lts.next competitor action := by
  simp [shift]

/-- The executable configuration enumeration is exactly the finite state powerset. -/
theorem mem_configs_iff (lts : CCS.FiniteLTS Action State)
    (state : State) (competitors : StateSet State) :
    (state, competitors) ∈ configs lts ↔
      state ∈ lts.states ∧ competitors ⊆ lts.states.toFinset := by
  constructor
  · intro hConfig
    rw [configs, List.mem_flatMap] at hConfig
    rcases hConfig with ⟨source, hSource, hConfig⟩
    rw [List.mem_map] at hConfig
    rcases hConfig with ⟨candidate, hCandidate, hEqual⟩
    have hCandidateSubset := powerset_member_subset lts.states candidate hCandidate
    cases hEqual
    exact ⟨hSource, hCandidateSubset⟩
  · rintro ⟨hState, hCompetitors⟩
    rw [configs, List.mem_flatMap]
    refine ⟨state, hState, ?_⟩
    rw [List.mem_map]
    exact ⟨competitors, subset_mem_powerset lts.states competitors hCompetitors, rfl⟩

/-- Shifting listed competitors through a realized finite LTS remains in its state domain. -/
theorem shift_subset_states
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (competitors : StateSet State)
    (action : Action)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    shift lts competitors action ⊆ lts.states.toFinset := by
  intro target hTarget
  rcases (mem_shift_iff lts competitors action target).mp hTarget with
    ⟨competitor, hCompetitor, hNext⟩
  have hCompetitorState : competitor ∈ lts.states := by
    simpa using hCompetitors hCompetitor
  simpa using realizes.next_closed competitor action target hCompetitorState hNext

/-- Decoding an executable shift agrees with the semantic lifted derivative. -/
theorem decodeSet_shift_iff
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (competitors : StateSet State)
    (action : Action)
    (process : CCS Action Name)
    (hCompetitors : ∀ competitor, competitor ∈ competitors → competitor ∈ lts.states) :
    CCS.FiniteLTS.decodeSet decode (shift lts competitors action) process ↔
      DerivSetOf env (CCS.FiniteLTS.decodeSet decode competitors) action process := by
  constructor
  · rintro ⟨target, hTarget, hDecode⟩
    rcases (mem_shift_iff lts competitors action target).mp hTarget with
      ⟨competitor, hCompetitor, hNext⟩
    refine ⟨decode competitor, ⟨competitor, hCompetitor, rfl⟩, ?_⟩
    simpa [hDecode] using realizes.next_sound competitor action target hNext
  · rintro ⟨source, ⟨competitor, hCompetitor, hDecode⟩, hDeriv⟩
    subst source
    rcases realizes.next_complete competitor action process
      (hCompetitors competitor hCompetitor) hDeriv with
      ⟨target, _, hTarget, hTargetDecode⟩
    exact ⟨target, (mem_shift_iff lts competitors action target).mpr
      ⟨competitor, hCompetitor, hTarget⟩, hTargetDecode⟩

/-- One Boolean Trace marker step is sound for the semantic abstract transformer. -/
theorem marks_sound
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (marked : MarkerTable State)
    (state : State)
    (competitors : StateSet State)
    (hConfig : (state, competitors) ∈ configs lts)
    (hMarked : marks lts marked state competitors = true)
    (hSound : ∀ successor shifted,
      configMem (successor, shifted) marked = true →
        AbstractDiff env (decode successor) (CCS.FiniteLTS.decodeSet decode shifted)) :
    AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors) := by
  rcases (mem_configs_iff lts state competitors).mp hConfig with ⟨_, hCompetitors⟩
  simp only [marks, Bool.or_eq_true, decide_eq_true_eq] at hMarked
  rcases hMarked with hEmpty | hStep
  · subst competitors
    have hDecodeEmpty : CCS.FiniteLTS.decodeSet decode (∅ : StateSet State) =
        (fun _ => False) := by
      funext process
      apply propext
      constructor
      · rintro ⟨source, hSource, _⟩
        grind
      · exact False.elim
    rw [hDecodeEmpty]
    exact abstractDiff_empty env (decode state)
  · rcases List.any_eq_true.mp hStep with ⟨action, _, hSuccessors⟩
    rcases List.any_eq_true.mp hSuccessors with ⟨successor, hSuccessor, hPrevious⟩
    apply lfpDTrSharp_prefixpoint env (decode state)
      (CCS.FiniteLTS.decodeSet decode competitors)
    refine Or.inr ⟨action, decode successor, realizes.next_sound state action successor hSuccessor, ?_⟩
    have hShift : CCS.FiniteLTS.decodeSet decode (shift lts competitors action) =
        DerivSetOf env (CCS.FiniteLTS.decodeSet decode competitors) action := by
      funext process
      apply propext
      exact decodeSet_shift_iff lts env decode realizes competitors action process
        (fun competitor hCompetitor => by simpa using hCompetitors hCompetitor)
    simpa only [hShift] using hSound successor (shift lts competitors action) hPrevious

/-- Every configuration in an executable saturation round is drawn from the enumeration. -/
theorem saturateN_subset_configs (lts : CCS.FiniteLTS Action State) (count : Nat) :
    saturateN (configs lts) configMem (fun marked config => marks lts marked config.1 config.2) count
      ⊆ configs lts := by
  induction count with
  | zero => simp [saturateN]
  | succ count ih =>
      intro config hConfig
      simp only [saturateN, saturateStep, List.mem_append, List.mem_filter,
        Bool.and_eq_true] at hConfig
      rcases hConfig with hPrevious | hNew
      · exact ih hPrevious
      · exact hNew.1

/-- Each finite saturation approximation is semantically sound. -/
theorem saturateN_sound
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (count : Nat)
    (state : State)
    (competitors : StateSet State)
    (hMember : (state, competitors) ∈
      saturateN (configs lts) configMem
        (fun marked config => marks lts marked config.1 config.2) count) :
    AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors) := by
  induction count generalizing state competitors with
  | zero => simp [saturateN] at hMember
  | succ count ih =>
      simp only [saturateN, saturateStep, List.mem_append, List.mem_filter,
        Bool.and_eq_true] at hMember
      rcases hMember with hPrevious | hNew
      · exact ih state competitors hPrevious
      · exact marks_sound lts env decode realizes
          (saturateN (configs lts) configMem
            (fun marked config => marks lts marked config.1 config.2) count)
          state competitors hNew.1 hNew.2.2
          (fun successor shifted hMember =>
            ih successor shifted ((configMem_iff (successor, shifted) _).mp hMember))

/-- The executable Trace result implies the semantic abstract difference. -/
theorem abstractDiff_sound
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hAbstractDiff : abstractDiff lts state competitors = true) :
    AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors) := by
  unfold abstractDiff markerTable saturate at hAbstractDiff
  exact saturateN_sound lts env decode realizes (configs lts).length state competitors
    ((configMem_iff (state, competitors) _).mp hAbstractDiff)

/-- Proof-facing form of one Trace marker rule. -/
def marksSet (lts : CCS.FiniteLTS Action State) (marked : Set (Config State))
    (config : Config State) : Prop :=
  config.2 = ∅ ∨ ∃ action ∈ lts.actions, ∃ successor ∈ lts.next config.1 action,
    (successor, shift lts config.2 action) ∈ marked

/-- The Boolean Trace marker rule reflects its proof-facing form. -/
theorem marks_iff_marksSet (lts : CCS.FiniteLTS Action State)
    (marked : MarkerTable State) (state : State) (competitors : StateSet State) :
    marks lts marked state competitors = true ↔
      marksSet lts (marked.toFinset : Set (Config State)) (state, competitors) := by
  simp only [marks, marksSet, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro (hEmpty | ⟨action, hAction, successor, hSuccessor, hMarked⟩)
    · exact Or.inl hEmpty
    · exact Or.inr ⟨action, hAction, successor, hSuccessor,
        by simpa using (configMem_iff (successor, shift lts competitors action) marked).mp hMarked⟩
  · rintro (hEmpty | ⟨action, hAction, successor, hSuccessor, hMarked⟩)
    · exact Or.inl hEmpty
    · exact Or.inr ⟨action, hAction, successor, hSuccessor,
        (configMem_iff (successor, shift lts competitors action) marked).mpr (by simpa using hMarked)⟩

/-- The proof-facing Trace marker relation is monotone in its table argument. -/
theorem marksSet_mono (lts : CCS.FiniteLTS Action State) {left right : Set (Config State)}
    (hSubset : left ⊆ right) (config : Config State) :
    marksSet lts left config → marksSet lts right config := by
  rintro (hEmpty | ⟨action, hAction, successor, hSuccessor, hMarked⟩)
  · exact Or.inl hEmpty
  · exact Or.inr ⟨action, hAction, successor, hSuccessor, hSubset hMarked⟩

/-- The executable Trace marker table denotes the generic least marker table. -/
theorem markerTable_toFinset_eq_tableLfp (lts : CCS.FiniteLTS Action State) :
    ((markerTable lts).toFinset : Set (Config State)) =
      tableLfp (configs lts).toFinset (marksSet lts)
        (fun hSubset config hMarks => marksSet_mono lts hSubset config hMarks) := by
  unfold markerTable
  exact saturate_toFinset_eq_tableLfp (configs lts) configMem
    (fun marked config => marks lts marked config.1 config.2) (marksSet lts)
    (fun config marked => configMem_iff config marked)
    (fun marked config => marks_iff_marksSet lts marked config.1 config.2)
    (fun hSubset config hMarks => marksSet_mono lts hSubset config hMarks)

/-- A configuration satisfying the Trace marker rule belongs to the final marker table. -/
theorem markerTable_closed (lts : CCS.FiniteLTS Action State)
    (state : State) (competitors : StateSet State)
    (hConfig : (state, competitors) ∈ configs lts)
    (hMarked : marks lts (markerTable lts) state competitors = true) :
    configMem (state, competitors) (markerTable lts) = true := by
  apply (configMem_iff (state, competitors) (markerTable lts)).mpr
  have hConfigSet : (state, competitors) ∈ ((configs lts).toFinset : Set (Config State)) :=
    by simpa using hConfig
  have hMarkedSet : marksSet lts ((markerTable lts).toFinset : Set (Config State))
      (state, competitors) :=
    (marks_iff_marksSet lts (markerTable lts) state competitors).mp hMarked
  rw [markerTable_toFinset_eq_tableLfp lts] at hMarkedSet
  have hLfpMember : (state, competitors) ∈
      tableLfp (configs lts).toFinset (marksSet lts)
        (fun hSubset config hMarks => marksSet_mono lts hSubset config hMarks) := by
    rw [← tableStep_tableLfp (configs lts).toFinset (marksSet lts)
      (fun hSubset config hMarks => marksSet_mono lts hSubset config hMarks)]
    exact Or.inr ⟨hConfigSet, hMarkedSet⟩
  rw [← markerTable_toFinset_eq_tableLfp lts] at hLfpMember
  simpa using hLfpMember

/-- Semantic pairs represented by the finite model inherit the final marker-table result. -/
def markerPredicate
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (decode : State → CCS Action Name) :
    AbsDiffSys Action Name :=
  fun process processes => ∀ state competitors,
    state ∈ lts.states →
    competitors ⊆ lts.states.toFinset →
    process = decode state →
    processes = CCS.FiniteLTS.decodeSet decode competitors →
    configMem (state, competitors) (markerTable lts) = true

/-- `markerPredicate` is a semantic pre-fixpoint of the Trace abstract transformer. -/
theorem markerPredicate_prefixpoint
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode) :
    ∀ process processes,
      DTrSharp env (markerPredicate lts decode) process processes →
        markerPredicate lts decode process processes := by
  intro process processes hSharp state competitors hState hCompetitors hProcess hProcesses
  subst process
  subst processes
  rcases hSharp with hEmpty | ⟨action, successorProcess, hDeriv, hNext⟩
  · have hCompetitorsEmpty : competitors = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro competitor hCompetitor
      exact hEmpty (decode competitor) ⟨competitor, hCompetitor, rfl⟩
    apply markerTable_closed lts state competitors
      ((mem_configs_iff lts state competitors).mpr ⟨hState, hCompetitors⟩)
    simp [marks, hCompetitorsEmpty]
  · rcases realizes.next_complete state action successorProcess hState hDeriv with
      ⟨successor, hSuccessorState, hSuccessor, hDecodeSuccessor⟩
    have hShifted : shift lts competitors action ⊆ lts.states.toFinset :=
      shift_subset_states lts env decode realizes competitors action hCompetitors
    have hDecodeShift : CCS.FiniteLTS.decodeSet decode (shift lts competitors action) =
        DerivSetOf env (CCS.FiniteLTS.decodeSet decode competitors) action := by
      funext target
      apply propext
      exact decodeSet_shift_iff lts env decode realizes competitors action target
        (fun competitor hCompetitor => by simpa using hCompetitors hCompetitor)
    have hPrevious : configMem (successor, shift lts competitors action) (markerTable lts) = true :=
      hNext successor (shift lts competitors action) hSuccessorState hShifted
        hDecodeSuccessor.symm hDecodeShift.symm
    apply markerTable_closed lts state competitors
      ((mem_configs_iff lts state competitors).mpr ⟨hState, hCompetitors⟩)
    simp only [marks, Bool.or_eq_true]
    exact Or.inr (List.any_eq_true.mpr ⟨action, realizes.action_complete action,
      List.any_eq_true.mpr ⟨successor, hSuccessor, hPrevious⟩⟩)

/-- The semantic Trace abstract difference is computed by the final marker table on represented inputs. -/
theorem abstractDiff_complete
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset)
    (hAbstractDiff : AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors)) :
    abstractDiff lts state competitors = true := by
  have hMarker := hAbstractDiff (markerPredicate lts decode)
    (markerPredicate_prefixpoint lts env decode realizes)
  unfold markerPredicate at hMarker
  unfold abstractDiff markerTable saturate
  exact hMarker state competitors hState hCompetitors rfl rfl

/-- The executable and semantic Trace abstract differences agree on represented inputs. -/
theorem abstractDiff_iff
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    abstractDiff lts state competitors = true ↔
      AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors) := by
  constructor
  · exact abstractDiff_sound lts env decode realizes state competitors
  · exact abstractDiff_complete lts env decode realizes state competitors hState hCompetitors

/--
Certificate that a finite transition system realizes its decoded CCS model.
The executable/semantic correspondence is derived by `abstractDiff_correct`.
-/
structure AbstractDiffCorrect
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name) : Prop where
  realizes : CCS.FiniteLTS.Realizes lts env decode

/-- A realization supplies the Trace evaluator correctness certificate. -/
def abstractDiffCorrect_of_realizes
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode) :
    AbstractDiffCorrect lts env decode :=
  ⟨realizes⟩

/-- Generic connection from a realized executable finite model to `AbstractDiff`. -/
theorem abstractDiff_correct
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (certificate : AbstractDiffCorrect lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    abstractDiff lts state competitors = true ↔
      AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors) :=
  abstractDiff_iff lts env decode certificate.realizes state competitors hState hCompetitors

end FiniteLTS
end EqCheckingAbstractInterpretation.Trace
