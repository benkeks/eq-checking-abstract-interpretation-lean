import EqCheckingAbstractInterpretation.FiniteEvaluator.Correctness
import EqCheckingAbstractInterpretation.Trace.FiniteEvaluator
import EqCheckingAbstractInterpretation.Trace.Correctness

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.FiniteEvaluator

universe u v w

namespace FiniteLTS

variable {Action : Type u} {State : Type v}
  [DecidableEq Action] [DecidableEq State]

/-- Boolean marker-table membership reflects ordinary list membership. -/
lemma configMem_iff (config : Config State) (marked : MarkerTable State) :
    configMem config marked = true ↔ config ∈ marked := by
  induction marked with
  | nil => simp [configMem]
  | cons entry marked ih => simp only [configMem, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, ih]; grind

/-- Membership in a shifted competitor set comes from one competitor transition row. -/
lemma mem_shift_iff (lts : CCS.FiniteLTS Action State) (competitors : StateSet State)
    (action : Action) (target : State) :
    target ∈ shift lts competitors action ↔
      ∃ competitor ∈ competitors, target ∈ lts.next competitor action := by
  simp [shift]

/-- The executable configuration enumeration is exactly the finite state powerset. -/
lemma mem_configs_iff (lts : CCS.FiniteLTS Action State)
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

lemma successors_closed (lts : CCS.FiniteLTS Action State)
    (hNextClosed : ∀ state action target, state ∈ lts.states →
      target ∈ lts.next state action → target ∈ lts.states)
    (config successor : Config State)
    (hConfig : config ∈ configs lts)
    (hSuccessor : successor ∈ successors lts config) :
    successor ∈ configs lts := by
  rcases config with ⟨state, competitors⟩
  rcases (mem_configs_iff lts state competitors).mp hConfig with ⟨hState, hCompetitors⟩
  simp only [successors, List.mem_flatMap, List.mem_map] at hSuccessor
  rcases hSuccessor with ⟨action, _, target, hTarget, rfl⟩
  apply (mem_configs_iff lts target (shift lts competitors action)).mpr
  constructor
  · exact hNextClosed state action target hState hTarget
  · intro next hNext
    rcases (mem_shift_iff lts competitors action next).mp hNext with
      ⟨competitor, hCompetitor, hDerivative⟩
    simpa using hNextClosed competitor action next
      (by simpa using hCompetitors hCompetitor) hDerivative

private lemma powerset_length (states : List State) :
    (powerset states).length = 2 ^ states.length := by
  induction states with
  | nil => simp [powerset]
  | cons state states ih =>
    change ((powerset states) ++ (powerset states).map (fun set => insert state set)).length =
      2 ^ (states.length + 1)
    simp only [List.length_append, List.length_map, ih, pow_succ]
    omega

private lemma configs_length (lts : CCS.FiniteLTS Action State) :
    (configs lts).length = lts.states.length * 2 ^ lts.states.length := by
  simp [configs, List.length_flatMap, powerset_length]

private lemma reachUntil_contains (lts : CCS.FiniteLTS Action State)
    (fuel : Nat) (seen : MarkerTable State) (config : Config State)
    (hConfig : config ∈ seen) : config ∈ reachUntil lts fuel seen := by
  induction fuel generalizing seen with
  | zero => exact hConfig
  | succ fuel ih =>
    simp only [reachUntil]
    split_ifs
    · exact hConfig
    · exact ih _ (List.mem_append.mpr (Or.inl hConfig))

private lemma reachUntil_subset_closed (lts : CCS.FiniteLTS Action State)
    (closed : Set (Config State))
    (hClosed : ∀ config ∈ closed, ∀ successor ∈ successors lts config,
      successor ∈ closed)
    (fuel : Nat) (seen : MarkerTable State)
    (hSeen : ∀ config ∈ seen, config ∈ closed) :
    ∀ config ∈ reachUntil lts fuel seen, config ∈ closed := by
  induction fuel generalizing seen with
  | zero => exact hSeen
  | succ fuel ih =>
    simp only [reachUntil]
    split_ifs
    · exact hSeen
    · apply ih
      intro config hConfig
      rcases List.mem_append.mp hConfig with hOld | hNew
      · exact hSeen config hOld
      · rcases List.mem_filter.mp (List.mem_eraseDups.mp hNew) with ⟨hFlat, _⟩
        rcases List.mem_flatMap.mp hFlat with ⟨source, hSource, hSuccessor⟩
        exact hClosed source (hSeen source hSource) config hSuccessor

private lemma reachUntil_successor_closed (lts : CCS.FiniteLTS Action State)
    (domain : Finset (Config State))
    (hDomainClosed : ∀ config ∈ domain, ∀ successor ∈ successors lts config,
      successor ∈ domain)
    (fuel : Nat) (seen : MarkerTable State)
    (hSeen : ∀ config ∈ seen, config ∈ domain)
    (hEnough : domain.card - seen.toFinset.card < fuel) :
    ∀ config ∈ reachUntil lts fuel seen,
      ∀ successor ∈ successors lts config,
        successor ∈ reachUntil lts fuel seen := by
  induction fuel generalizing seen with
  | zero => omega
  | succ fuel ih =>
    simp only [reachUntil]
    split_ifs with hFresh
    · intro config hConfig successor hSuccessor
      by_contra hMissing
      have hNotMem : (configMem successor seen) = false := by
        cases hBool : configMem successor seen with
        | false => rfl
        | true => exact False.elim (hMissing ((configMem_iff successor seen).mp hBool))
      have hNew : successor ∈ (seen.flatMap (successors lts)).filter
          (fun candidate => !configMem candidate seen) := List.mem_filter.mpr
        ⟨List.mem_flatMap.mpr ⟨config, hConfig, hSuccessor⟩, by simp [hNotMem]⟩
      rw [List.isEmpty_iff.mp hFresh] at hNew
      simp at hNew
    · let fresh := (seen.flatMap (successors lts)).filter
          (fun config => !configMem config seen)
      let next := seen ++ fresh.eraseDups
      have hFreshNonempty : fresh ≠ [] := by
        intro hNil
        exact hFresh (by simp [fresh, hNil])
      obtain ⟨candidate, hCandidate⟩ := List.exists_mem_of_ne_nil fresh hFreshNonempty
      have hCandidateMissing : candidate ∉ seen := by
        intro hMember
        have hNotMem := (List.mem_filter.mp hCandidate).2
        have hMem := (configMem_iff candidate seen).mpr hMember
        simp [hMem] at hNotMem
      have hCandidateNext : candidate ∈ next :=
        List.mem_append.mpr (Or.inr (List.mem_eraseDups.mpr hCandidate))
      have hSubset : seen.toFinset ⊆ next.toFinset := by
        intro config hConfig
        exact List.mem_toFinset.mpr (List.mem_append.mpr
          (Or.inl (List.mem_toFinset.mp hConfig)))
      have hStrict : seen.toFinset.card < next.toFinset.card := by
        apply Finset.card_lt_card
        apply (Finset.ssubset_iff_subset_ne).mpr
        refine ⟨hSubset, ?_⟩
        intro hEqual
        apply hCandidateMissing
        apply List.mem_toFinset.mp
        rw [hEqual]
        exact List.mem_toFinset.mpr hCandidateNext
      have hNextDomain : ∀ config ∈ next, config ∈ domain := by
        intro config hConfig
        rcases List.mem_append.mp hConfig with hOld | hNew
        · exact hSeen config hOld
        · rcases List.mem_filter.mp (List.mem_eraseDups.mp hNew) with ⟨hFlat, _⟩
          rcases List.mem_flatMap.mp hFlat with ⟨source, hSource, hSuccessor⟩
          exact hDomainClosed source (hSeen source hSource) config hSuccessor
      have hNextEnough : domain.card - next.toFinset.card < fuel := by
        have hBound := Finset.card_le_card (show next.toFinset ⊆ domain from
          fun config hConfig => hNextDomain config (List.mem_toFinset.mp hConfig))
        omega
      exact ih next hNextDomain hNextEnough

private lemma reachableConfigs_spec (lts : CCS.FiniteLTS Action State)
    (hNextClosed : ∀ state action target, state ∈ lts.states →
      target ∈ lts.next state action → target ∈ lts.states)
    (initial : Config State) (hInitial : initial ∈ configs lts) :
    (∀ config ∈ reachableConfigs lts initial, config ∈ configs lts) ∧
    initial ∈ reachableConfigs lts initial ∧
    (∀ config ∈ reachableConfigs lts initial,
      ∀ successor ∈ successors lts config,
        successor ∈ reachableConfigs lts initial) := by
  let domain := (configs lts).toFinset
  have hDomainClosed : ∀ config ∈ domain, ∀ successor ∈ successors lts config,
      successor ∈ domain := by
    intro config hConfig successor hSuccessor
    exact List.mem_toFinset.mpr (successors_closed lts hNextClosed config successor
      (List.mem_toFinset.mp hConfig) hSuccessor)
  have hBound : domain.card ≤ lts.states.length * 2 ^ lts.states.length := by
    calc
      domain.card ≤ (configs lts).length := List.toFinset_card_le (configs lts)
      _ = _ := configs_length lts
  have hEnough : domain.card - ([initial].toFinset).card <
      lts.states.length * 2 ^ lts.states.length + 1 := by omega
  constructor
  · intro config hConfig
    exact List.mem_toFinset.mp
      (reachUntil_subset_closed lts (domain : Set (Config State))
        (fun source hSource successor hSuccessor =>
          hDomainClosed source hSource successor hSuccessor)
        _ [initial] (by
          intro source hSource
          simp only [List.mem_singleton] at hSource
          subst source
          exact List.mem_toFinset.mpr hInitial) config hConfig)
  constructor
  · exact reachUntil_contains lts _ [initial] initial (by simp)
  · apply reachUntil_successor_closed lts domain hDomainClosed _ [initial]
    · intro source hSource
      simp only [List.mem_singleton] at hSource
      subst source
      exact List.mem_toFinset.mpr hInitial
    · exact hEnough

/-- Decoding an executable shift agrees with the semantic lifted derivative. -/
lemma decodeSet_shift_iff
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
lemma marks_sound
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

/-- Each finite saturation approximation is semantically sound. -/
lemma saturateN_sound
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
lemma abstractDiff_sound
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
lemma marks_iff_marksSet (lts : CCS.FiniteLTS Action State)
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
lemma marksSet_mono (lts : CCS.FiniteLTS Action State) {left right : Set (Config State)}
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

private lemma tableLfp_restrict (lts : CCS.FiniteLTS Action State)
    (domain relevant : Finset (Config State))
    (hSubset : relevant ⊆ domain)
    (hClosed : ∀ config ∈ relevant, ∀ successor ∈ successors lts config,
      successor ∈ relevant)
    (config : Config State) (hConfig : config ∈ relevant) :
    config ∈ tableLfp (domain : Set (Config State)) (marksSet lts)
      (fun h config hMarks => marksSet_mono lts h config hMarks) ↔
    config ∈ tableLfp (relevant : Set (Config State)) (marksSet lts)
      (fun h config hMarks => marksSet_mono lts h config hMarks) := by
  let global := tableLfp (domain : Set (Config State)) (marksSet lts)
    (fun h config hMarks => marksSet_mono lts h config hMarks)
  let localTable := tableLfp (relevant : Set (Config State)) (marksSet lts)
    (fun h config hMarks => marksSet_mono lts h config hMarks)
  have hLocalSubset : localTable ⊆ global := by
    apply tableLfp_subset_of_prefixed _ _ _ global
    intro candidate hCandidate
    rcases hCandidate with hOld | ⟨hRelevant, hMarks⟩
    · exact hOld
    · have hStep : candidate ∈ tableStep (domain : Set (Config State))
          (marksSet lts) global := Or.inr ⟨hSubset hRelevant, hMarks⟩
      rw [tableStep_tableLfp (domain : Set (Config State)) (marksSet lts)
        (fun h config hMarks => marksSet_mono lts h config hMarks)] at hStep
      exact hStep
  let upper : Set (Config State) := { candidate | candidate ∉ relevant ∨ candidate ∈ localTable }
  have hGlobalSubset : global ⊆ upper := by
    apply tableLfp_subset_of_prefixed _ _ _ upper
    intro candidate hCandidate
    by_cases hRelevant : candidate ∈ relevant
    · right
      rcases hCandidate with hOld | ⟨_, hMarks⟩
      · exact hOld.resolve_left (fun hNot => hNot hRelevant)
      · have hLocalMarks : marksSet lts localTable candidate := by
          rcases hMarks with hEmpty | ⟨action, hAction, successor, hNext, hUpper⟩
          · exact Or.inl hEmpty
          · have hSuccessor : (successor, shift lts candidate.2 action) ∈
                successors lts candidate := by
              rcases candidate with ⟨state, competitors⟩
              exact List.mem_flatMap.mpr ⟨action, hAction,
                List.mem_map.mpr ⟨successor, hNext, rfl⟩⟩
            have hSuccessorRelevant := hClosed candidate hRelevant
              (successor, shift lts candidate.2 action) hSuccessor
            exact Or.inr ⟨action, hAction, successor, hNext,
              hUpper.resolve_left (fun hNot => hNot hSuccessorRelevant)⟩
        have hStep : candidate ∈ tableStep (relevant : Set (Config State))
          (marksSet lts) localTable := Or.inr ⟨hRelevant, hLocalMarks⟩
        rw [tableStep_tableLfp (relevant : Set (Config State)) (marksSet lts)
          (fun h config hMarks => marksSet_mono lts h config hMarks)] at hStep
        exact hStep
    · exact Or.inl hRelevant
  constructor
  · intro hGlobal
    exact (hGlobalSubset hGlobal).resolve_left (fun hNot => hNot hConfig)
  · intro hLocal
    exact hLocalSubset hLocal

/-- Query-local evaluation agrees with the full marker table on closed finite models. -/
theorem abstractDiffReachable_eq_abstractDiff (lts : CCS.FiniteLTS Action State)
    (hNextClosed : ∀ source action target, source ∈ lts.states →
      target ∈ lts.next source action → target ∈ lts.states)
    (state : State) (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    abstractDiffReachable lts state competitors = abstractDiff lts state competitors := by
  let query : Config State := (state, competitors)
  let relevant := reachableConfigs lts query
  have hQuery : query ∈ configs lts :=
    (mem_configs_iff lts state competitors).mpr ⟨hState, hCompetitors⟩
  obtain ⟨hSubset, hInitial, hClosed⟩ := reachableConfigs_spec lts hNextClosed query hQuery
  have hRelevantSubset : relevant.toFinset ⊆ (configs lts).toFinset := by
    intro config hConfig
    exact List.mem_toFinset.mpr (hSubset config (List.mem_toFinset.mp hConfig))
  have hRelevantClosed : ∀ config ∈ relevant.toFinset,
      ∀ successor ∈ successors lts config, successor ∈ relevant.toFinset := by
    intro config hConfig successor hSuccessor
    exact List.mem_toFinset.mpr (hClosed config (List.mem_toFinset.mp hConfig)
      successor hSuccessor)
  have hLocalTable := saturate_toFinset_eq_tableLfp relevant configMem
    (fun marked config => marks lts marked config.1 config.2) (marksSet lts)
    (fun config marked => configMem_iff config marked)
    (fun marked config => marks_iff_marksSet lts marked config.1 config.2)
    (fun h config hMarks => marksSet_mono lts h config hMarks)
  apply Bool.eq_iff_iff.mpr
  change configMem query (saturate relevant configMem
      (fun marked config => marks lts marked config.1 config.2)) = true ↔
    configMem query (markerTable lts) = true
  rw [configMem_iff, configMem_iff, ← List.mem_toFinset, ← List.mem_toFinset]
  change query ∈ ((saturate relevant configMem
      (fun marked config => marks lts marked config.1 config.2)).toFinset : Set (Config State)) ↔
    query ∈ ((markerTable lts).toFinset : Set (Config State))
  rw [hLocalTable, markerTable_toFinset_eq_tableLfp]
  exact (tableLfp_restrict lts (configs lts).toFinset relevant.toFinset
    hRelevantSubset hRelevantClosed query (List.mem_toFinset.mpr hInitial)).symm

/-- A configuration satisfying the Trace marker rule belongs to the final marker table. -/
lemma markerTable_closed (lts : CCS.FiniteLTS Action State)
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
lemma markerPredicate_prefixpoint
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
    have hShifted : shift lts competitors action ⊆ lts.states.toFinset := by
      intro target hTarget
      rcases (mem_shift_iff lts competitors action target).mp hTarget with
        ⟨competitor, hCompetitor, hNext⟩
      simpa using realizes.next_closed competitor action target
        (by simpa using hCompetitors hCompetitor) hNext
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
lemma abstractDiff_complete
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

/-- The executable query-local marker agrees with CCS trace semantics. -/
theorem abstractDiffReachable_correct
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (certificate : AbstractDiffCorrect lts env decode)
    (state : State) (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    abstractDiffReachable lts state competitors = true ↔
      AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors) := by
  rw [abstractDiffReachable_eq_abstractDiff lts certificate.realizes.next_closed state
    competitors hState hCompetitors]
  exact abstractDiff_correct lts env decode certificate state competitors hState hCompetitors

/-- The executable Boolean preorder agrees with semantic trace inclusion. -/
theorem tracePreordered_correct
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (certificate : AbstractDiffCorrect lts env decode)
    (left right : State)
    (hLeft : left ∈ lts.states)
    (hRight : right ∈ lts.states) :
    tracePreordered lts left right = true ↔
      TracePreorder env (decode left) (decode right) := by
  have hSingleton : ({right} : StateSet State) ⊆ lts.states.toFinset := by
    simpa using hRight
  have hDecode : CCS.FiniteLTS.decodeSet decode ({right} : StateSet State) =
      ({decode right} : ProcSet Action Name) := by
    funext process
    apply propext
    simp only [CCS.FiniteLTS.decodeSet, Finset.mem_singleton, exists_eq_left]
    change decode right = process ↔ process ∈ ({decode right} : Set (CCS Action Name))
    simp only [Set.mem_singleton_iff, eq_comm]
  have hDiff := abstractDiffReachable_correct lts env decode certificate left {right}
    hLeft hSingleton
  rw [hDecode] at hDiff
  rw [tracePreorder_iff_no_marker]
  change tracePreordered lts left right = true ↔
    ¬ AbstractDiff env (decode left) ({decode right} : ProcSet Action Name)
  constructor
  · intro hPre hMarker
    have hBool := hDiff.mpr hMarker
    simp [tracePreordered, hBool] at hPre
  · intro hNoMarker
    have hFalse : abstractDiffReachable lts left {right} = false := by
      cases hBool : abstractDiffReachable lts left {right} with
      | false => rfl
      | true => exact False.elim (hNoMarker (hDiff.mp hBool))
    simp [tracePreordered, hFalse]

end FiniteLTS
end EqCheckingAbstractInterpretation.Trace
