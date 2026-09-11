import EqCheckingAbstractInterpretation.CCS.FiniteLTS
import EqCheckingAbstractInterpretation.FiniteEvaluator.Correctness
import EqCheckingAbstractInterpretation.Ready.AbstractTransformer
import EqCheckingAbstractInterpretation.Ready.FiniteEvaluator

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.FiniteEvaluator

universe u v w

namespace FiniteLTS

variable {Action : Type u} {State : Type v}
  [DecidableEq Action] [DecidableEq State]

/-- Membership in a shifted competitor set is precisely membership in one transition row. -/
lemma mem_shift_iff (lts : CCS.FiniteLTS Action State) (competitors : StateSet State)
    (action : Action) (target : State) :
    target ∈ shift lts competitors action ↔
      ∃ competitor ∈ competitors, target ∈ lts.next competitor action := by
  simp [shift]

/-- The finite configuration universe is exactly the represented state powerset. -/
lemma mem_configUniverse_iff (lts : CCS.FiniteLTS Action State)
    (state : State) (competitors : StateSet State) :
    (state, competitors) ∈ configUniverse lts ↔
      state ∈ lts.states ∧ competitors ⊆ lts.states.toFinset := by
  constructor
  · intro hConfig
    rw [configUniverse, List.mem_flatMap] at hConfig
    rcases hConfig with ⟨source, hSource, hConfig⟩
    rw [List.mem_map] at hConfig
    rcases hConfig with ⟨candidate, hCandidate, hEqual⟩
    have hCandidateSubset := powerset_member_subset lts.states candidate hCandidate
    cases hEqual
    exact ⟨hSource, hCandidateSubset⟩
  · rintro ⟨hState, hCompetitors⟩
    rw [configUniverse, List.mem_flatMap]
    refine ⟨state, hState, ?_⟩
    rw [List.mem_map]
    exact ⟨competitors, subset_mem_powerset lts.states competitors hCompetitors, rfl⟩

/-- The executable competitor list enumerates exactly the listed finite competitors. -/
lemma mem_competitorsOf_iff (lts : CCS.FiniteLTS Action State)
    (competitors : StateSet State) (state : State) :
    state ∈ competitorsOf lts competitors ↔ state ∈ lts.states ∧ state ∈ competitors := by
  simp [competitorsOf]

/-- `competitorsOf` inherits duplicate-freeness from the finite LTS state list. -/
lemma competitorsOf_nodup
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (competitors : StateSet State) :
    (competitorsOf lts competitors).Nodup := by
  exact realizes.states_nodup.filter _

/-- Generated Ready successor configurations remain inside the represented universe. -/
lemma configSuccessors_subset_configUniverse
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (config : ReadyConfig State)
    (hConfig : config ∈ configUniverse lts) :
    ∀ successor, successor ∈ configSuccessors lts config → successor ∈ configUniverse lts := by
  intro successor hSuccessor
  rcases (mem_configUniverse_iff lts config.1 config.2).mp hConfig with ⟨hState, _⟩
  rw [configSuccessors, List.mem_flatMap] at hSuccessor
  rcases hSuccessor with ⟨selected, hSelected, hActions⟩
  rw [List.mem_flatMap] at hActions
  rcases hActions with ⟨action, _, hTargets⟩
  rw [List.mem_map] at hTargets
  rcases hTargets with ⟨target, hTarget, rfl⟩
  have hSelectedSubset := powerset_member_subset (competitorsOf lts config.2) selected hSelected
  have hSelectedStates : selected ⊆ lts.states.toFinset := by
    intro competitor hCompetitor
    rcases (mem_competitorsOf_iff lts config.2 competitor).mp
      (by simpa using hSelectedSubset hCompetitor) with ⟨hListed, _⟩
    simpa using hListed
  have hShifted : shift lts selected action ⊆ lts.states.toFinset := by
    intro shifted hShifted
    rcases (mem_shift_iff lts selected action shifted).mp hShifted with
      ⟨competitor, hCompetitor, hNext⟩
    simpa using realizes.next_closed competitor action shifted
      (by simpa using hSelectedStates hCompetitor) hNext
  apply (mem_configUniverse_iff lts target (shift lts selected action)).mpr
  exact ⟨by simpa using realizes.next_closed config.1 action target hState hTarget, hShifted⟩

/--
`assignmentsWithSlots` enumerates exactly the assignments with one allowed
choice for every competitor.
-/
lemma mem_assignmentsWithSlots_iff
    (lts : CCS.FiniteLTS Action State)
    (slots : List Nat)
    (competitors : List State)
    (assignment : Assignment Action) :
    assignment ∈ assignmentsWithSlots lts slots competitors ↔
      assignment.length = competitors.length ∧
        ∀ choice, choice ∈ assignment → choice ∈ assignmentChoices lts slots := by
  induction competitors generalizing assignment with
  | nil =>
      constructor
      · intro h
        simp only [assignmentsWithSlots, List.mem_singleton] at h
        subst assignment
        exact ⟨rfl, fun choice hChoice => by simp at hChoice⟩
      · rintro ⟨hLength, _⟩
        cases assignment with
        | nil => simp [assignmentsWithSlots]
        | cons choice assignment => simp at hLength
  | cons competitor competitors ih =>
      constructor
      · intro h
        rw [assignmentsWithSlots, List.mem_flatMap] at h
        rcases h with ⟨tail, hTail, hAssignment⟩
        rw [List.mem_map] at hAssignment
        rcases hAssignment with ⟨choice, hChoice, rfl⟩
        rcases (ih tail).mp hTail with ⟨hLength, hChoices⟩
        refine ⟨by simp [hLength], ?_⟩
        intro other hOther
        rcases List.mem_cons.mp hOther with rfl | hOther
        · exact hChoice
        · exact hChoices other hOther
      · rintro ⟨hLength, hChoices⟩
        cases assignment with
        | nil => simp at hLength
        | cons choice tail =>
            rw [assignmentsWithSlots, List.mem_flatMap]
            refine ⟨tail, ?_, ?_⟩
            · apply (ih tail).mpr
              refine ⟨by simpa using hLength, ?_⟩
              intro other hOther
              exact hChoices other (by simp [hOther])
            · exact List.mem_map.mpr ⟨choice, hChoices choice (by simp), rfl⟩

/-- The non-negative choices contain exactly one listed slot, action, and capability. -/
lemma mem_assignmentChoices_iff
    (lts : CCS.FiniteLTS Action State)
    (slots : List Nat)
    (choice : Option (Nat × Action × Capability)) :
    choice ∈ assignmentChoices lts slots ↔ choice = none ∨
      ∃ slot ∈ slots, ∃ action ∈ lts.actions, ∃ capability ∈ capabilities,
        choice = some (slot, action, capability) := by
  simp [assignmentChoices]
  constructor
  · rintro (rfl | ⟨slot, hSlot, action, hAction, capability, hCapability, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨slot, hSlot, action, hAction, capability, hCapability, rfl⟩
  · rintro (rfl | ⟨slot, hSlot, action, hAction, capability, hCapability, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨slot, hSlot, action, hAction, capability, hCapability, rfl⟩

/-- `assignments` is the exhaustive assignment enumerator for its finite competitors. -/
lemma mem_assignments_iff
    (lts : CCS.FiniteLTS Action State)
    (competitors : StateSet State)
    (assignment : Assignment Action) :
    assignment ∈ assignments lts competitors ↔
      assignment.length = (competitorsOf lts competitors).length ∧
        ∀ choice, choice ∈ assignment →
          choice ∈ assignmentChoices lts (List.range (competitorsOf lts competitors).length) := by
  exact mem_assignmentsWithSlots_iff lts
    (List.range (competitorsOf lts competitors).length)
    (competitorsOf lts competitors) assignment

/-- Well-formed assignments give each slot one consistent action and capability label. -/
lemma assignmentWellFormed_sound
    (assignment : Assignment Action)
    (hWellFormed : assignmentWellFormed assignment = true)
    (slot otherSlot : Nat)
    (action otherAction : Action)
    (capability otherCapability : Capability)
    (hEntry : some (slot, action, capability) ∈ assignment)
    (hOtherEntry : some (otherSlot, otherAction, otherCapability) ∈ assignment)
    (hSlot : slot = otherSlot) :
    action = otherAction ∧ capability = otherCapability := by
  induction assignment with
  | nil => simp at hEntry
  | cons entry assignment ih =>
      cases entry with
      | none =>
          simp only [assignmentWellFormed] at hWellFormed
          exact ih hWellFormed (by simpa using hEntry) (by simpa using hOtherEntry)
      | some entry =>
          rcases entry with ⟨entrySlot, entryAction, entryCapability⟩
          simp only [assignmentWellFormed, Bool.and_eq_true] at hWellFormed
          have hChecked := hWellFormed.1
          have hTail := hWellFormed.2
          have hHeadTail : ∀ tailSlot tailAction tailCapability,
              some (tailSlot, tailAction, tailCapability) ∈ assignment →
              entrySlot = tailSlot →
                entryAction = tailAction ∧ entryCapability = tailCapability := by
            intro tailSlot tailAction tailCapability hMember hEqual
            have hCheck := List.all_eq_true.mp hChecked
              (some (tailSlot, tailAction, tailCapability)) hMember
            simp at hCheck
            rcases hCheck with hDifferent | ⟨hAction, hCapability⟩
            · exact False.elim (hDifferent hEqual)
            · exact ⟨hAction, hCapability⟩
          simp only [List.mem_cons] at hEntry hOtherEntry
          rcases hEntry with hEntry | hEntry <;> rcases hOtherEntry with hOtherEntry | hOtherEntry
          · cases hEntry
            cases hOtherEntry
            exact ⟨rfl, rfl⟩
          · cases hEntry
            exact hHeadTail otherSlot otherAction otherCapability hOtherEntry hSlot
          · cases hOtherEntry
            rcases hHeadTail slot action capability hEntry hSlot.symm with ⟨hAction, hCapability⟩
            exact ⟨hAction.symm, hCapability.symm⟩
          · exact ih hTail hEntry hOtherEntry

/-- Semantic condition imposed on one competitor by the negative assignment group. -/
def NegativeAssignmentCondition
    (lts : CCS.FiniteLTS Action State)
    (negative : List Action)
    (competitor : State)
    (choice : Option (Nat × Action × Capability)) : Prop :=
  choice = none →
    ∃ action, action ∈ negative ∧ (lts.next competitor action).isEmpty = false

/-- The Boolean negative-group validator is exactly its pointwise partition condition. -/
lemma negativeAssignmentValid_iff
    (lts : CCS.FiniteLTS Action State)
    (competitors : List State)
    (negative : List Action)
    (assignment : Assignment Action) :
    negativeAssignmentValid lts competitors negative assignment = true ↔
      List.Forall₂ (NegativeAssignmentCondition lts negative) competitors assignment := by
  induction competitors generalizing assignment with
  | nil =>
      cases assignment with
      | nil => simp [negativeAssignmentValid]
      | cons choice assignment =>
        cases choice <;> simp [negativeAssignmentValid]
  | cons competitor competitors ih =>
      cases assignment with
      | nil => simp [negativeAssignmentValid]
      | cons choice assignment =>
          cases choice with
          | none =>
              simp only [negativeAssignmentValid, Bool.and_eq_true]
              constructor
              · rintro ⟨hEnabled, hTail⟩
                refine List.Forall₂.cons ?_ ((ih assignment).mp hTail)
                intro _
                rcases List.any_eq_true.mp hEnabled with ⟨action, hAction, hEmpty⟩
                exact ⟨action, hAction, by simpa using hEmpty⟩
              · intro h
                cases h with
                | cons hHead hTail =>
                    refine ⟨?_, (ih assignment).mpr hTail⟩
                    rcases hHead rfl with ⟨action, hAction, hEmpty⟩
                    apply List.any_eq_true.mpr
                    exact ⟨action, hAction, by simpa using hEmpty⟩
          | some entry =>
              simp only [negativeAssignmentValid]
              constructor
              · intro h
                refine List.Forall₂.cons ?_ ((ih assignment).mp h)
                intro hNone
                cases hNone
              · intro h
                cases h with
                | cons _ hTail => exact (ih assignment).mpr hTail

/-- Decoding an executable shift is exactly the semantic lifted derivative. -/
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

/-- An empty transition row is exactly a disabled semantic action on listed states. -/
lemma next_isEmpty_iff_not_enabled
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State) (action : Action) (hState : state ∈ lts.states) :
    (lts.next state action).isEmpty = true ↔ ¬ Enabled env (decode state) action := by
  cases hNext : lts.next state action with
  | nil =>
      constructor
      · intro _ hEnabled
        rcases hEnabled with ⟨process, hDeriv⟩
        rcases realizes.next_complete state action process hState hDeriv with
          ⟨target, _, hTarget, _⟩
        rw [hNext] at hTarget
        simp at hTarget
      · intro _
        simp
  | cons target targets =>
      have hEnabled : Enabled env (decode state) action :=
        ⟨decode target, realizes.next_sound state action target (by simp [hNext])⟩
      simp [hEnabled]

/-- The executable refusal check is the negative premise of a Ready observation. -/
lemma refuses_iff
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State) (negative : List Action) (hState : state ∈ lts.states) :
    marks.refuses lts state negative = true ↔
      ∀ action, action ∈ negative → ¬ Enabled env (decode state) action := by
  simp only [marks.refuses, List.all_eq_true]
  constructor
  · intro h action hAction
    exact (next_isEmpty_iff_not_enabled lts env decode realizes state action hState).mp
      (h action hAction)
  · intro h action hAction
    exact (next_isEmpty_iff_not_enabled lts env decode realizes state action hState).mpr
      (h action hAction)

/-- Boolean capability comparison agrees with the semantic capability order. -/
lemma capLeBool_iff (left right : Capability) :
    capLeBool left right = true ↔ capLe left right := by
  cases left <;> cases right <;> simp [capLeBool, capLe]

/-- The capability order is antisymmetric. -/
lemma capLe_antisymm {left right : Capability}
    (hLeftRight : capLe left right) (hRightLeft : capLe right left) :
    left = right := by
  cases left <;> cases right <;> simp [capLe] at hLeftRight hRightLeft ⊢

/-- Equal minimal antichains follow from raw soundness and downward cofinality. -/
lemma minimalCap_iff_of_sound_and_cofinal
    (finite semantic : Capability → Prop)
    (hSound : ∀ capability, finite capability → semantic capability)
    (hCofinal : ∀ capability, semantic capability →
      ∃ finiteCapability, finite finiteCapability ∧ capLe finiteCapability capability)
    (capability : Capability) :
    minimalCap finite capability ↔ minimalCap semantic capability := by
  constructor
  · rintro ⟨hFinite, hMinimal⟩
    refine ⟨hSound capability hFinite, ?_⟩
    intro other hSemantic hOther
    rcases hCofinal other hSemantic with ⟨finiteOther, hFiniteOther, hFiniteOtherLe⟩
    exact capLe_trans (hMinimal finiteOther hFiniteOther
      (capLe_trans hFiniteOtherLe hOther)) hFiniteOtherLe
  · rintro ⟨hSemantic, hMinimal⟩
    rcases hCofinal capability hSemantic with ⟨finiteCapability, hFinite, hFiniteLe⟩
    have hCapabilityLe := hMinimal finiteCapability (hSound finiteCapability hFinite) hFiniteLe
    have hEqual : capability = finiteCapability := capLe_antisymm hCapabilityLe hFiniteLe
    subst finiteCapability
    refine ⟨hFinite, ?_⟩
    intro other hOther hOtherLe
    exact hMinimal other (hSound other hOther) hOtherLe

omit [DecidableEq Action] [DecidableEq State] in
/-- Grouped branch requirements bound the requirement of any matching semantic node. -/
lemma reqOfObs_branches_le
    (negative : List Action)
    (branches : List (Branch Action State))
    (observation : Branch Action State → RSObs Action)
    (hObservation : ∀ branch, branch ∈ branches →
      capLe (reqOfObs (observation branch)) branch.capability) :
    capLe
      (reqOfObs (.node (branches.map (fun branch => (branch.action, observation branch))) negative))
      (branchesRequirement negative branches)
     := by
  have hChildren : capLe
      (childrenReq (branches.map (fun branch => (branch.action, observation branch))))
      (branchCapabilities branches) := by
    induction branches with
    | nil => exact capLe_refl _
    | cons branch branches ih =>
        simp only [List.map, childrenReq, branchCapabilities]
        exact capJoin_mono (hObservation branch (by simp))
          (ih (fun other hOther => hObservation other (by simp [hOther])))
  simpa only [reqOfObs, branchesRequirement, List.length_map] using
    (capJoin_mono (capLe_refl (req (decide (1 < branches.length)) (!negative.isEmpty))) hChildren)

/-- Boolean configuration membership is ordinary membership in the table. -/
lemma configMem_iff (config : ReadyConfig State) (configs : List (ReadyConfig State)) :
    configMem config configs = true ↔ config ∈ configs := by
  induction configs with
  | nil => simp [configMem]
  | cons entry configs ih => simp only [configMem, Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]; grind

/-- Configuration insertion adds exactly its argument when it was absent. -/
lemma mem_configInsert_iff (config entry : ReadyConfig State)
    (configs : List (ReadyConfig State)) :
    entry ∈ configInsert config configs ↔ entry = config ∨ entry ∈ configs := by
  by_cases hConfig : config ∈ configs
  · rw [configInsert, if_pos ((configMem_iff config configs).mpr hConfig)]
    constructor
    · exact Or.inr
    · rintro (rfl | hEntry)
      · exact hConfig
      · exact hEntry
  · cases hMem : configMem config configs with
    | false => simp [configInsert, hMem]
    | true => exact False.elim (hConfig ((configMem_iff config configs).mp hMem))

/-- Configuration union denotes ordinary membership union. -/
lemma mem_configUnion_iff (entry : ReadyConfig State)
    (left right : List (ReadyConfig State)) :
    entry ∈ configUnion left right ↔ entry ∈ left ∨ entry ∈ right := by
  induction left generalizing right with
  | nil => simp [configUnion]
  | cons config left ih =>
      change entry ∈ configUnion left (configInsert config right) ↔ _
      rw [ih, mem_configInsert_iff]
      grind

/-- Boolean capability-table membership is ordinary membership in the table. -/
lemma capabilityConfigMem_iff (config : CapabilityConfig State)
    (marked : CapabilityTable State) :
    capabilityConfigMem config marked = true ↔ config ∈ marked := by
  induction marked with
  | nil => simp [capabilityConfigMem]
  | cons entry marked ih =>
      simp only [capabilityConfigMem, Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
      grind

/-- Boolean capability-table non-membership is ordinary non-membership. -/
lemma capabilityConfigMem_eq_false_iff (config : CapabilityConfig State)
    (marked : CapabilityTable State) :
    capabilityConfigMem config marked = false ↔ config ∉ marked := by
  constructor
  · intro hFalse hMember
    have hTrue := capabilityConfigMem_iff config marked |>.mpr hMember
    simp [hFalse] at hTrue
  · intro hAbsent
    cases hMem : capabilityConfigMem config marked with
    | false => rfl
    | true => exact False.elim (hAbsent (capabilityConfigMem_iff config marked |>.mp hMem))

/-- Boolean threshold lookup is table membership below that threshold. -/
lemma markedAt_iff (marked : CapabilityTable State) (config : ReadyConfig State)
    (threshold : Capability) :
    markedAt marked config threshold = true ↔
      ∃ capability, (config, capability) ∈ marked ∧ capLe capability threshold := by
  simp only [markedAt, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨entry, hEntry, ⟨hConfig, hLe⟩⟩
    rcases entry with ⟨entryConfig, capability⟩
    have hEntryConfig : entryConfig = config := Prod.ext hConfig.1 hConfig.2
    subst entryConfig
    exact ⟨capability, hEntry, capLeBool_iff capability threshold |>.mp hLe⟩
  · rintro ⟨capability, hMember, hLe⟩
    exact ⟨(config, capability), hMember,
      ⟨⟨rfl, rfl⟩, capLeBool_iff capability threshold |>.mpr hLe⟩⟩

/-- Positive branch validation is exactly a table witness for every grouped branch. -/
lemma branchesValid_iff
    (lts : CCS.FiniteLTS Action State)
    (marked : CapabilityTable State)
    (state : State)
    (branches : List (Branch Action State)) :
    branchesValid lts marked state branches = true ↔
      ∀ branch, branch ∈ branches →
        ∃ successor, successor ∈ lts.next state branch.action ∧
          ∃ capability, ((successor, shift lts branch.competitors branch.action), capability) ∈ marked ∧
            capLe capability branch.capability := by
  induction branches with
  | nil => simp [branchesValid]
  | cons branch branches ih =>
      simp [branchesValid, markedAt_iff, ih]

/-- Proof-facing form of one executable Ready marker step, independent of table order. -/
def marksSet
    (lts : CCS.FiniteLTS Action State)
    (marked : Set (CapabilityConfig State))
    (config : ReadyConfig State)
    (capability : Capability) : Prop :=
  (config.2 = ∅ ∧ capability = .T) ∨
    ∃ negative, negative ∈ listPowerset lts.actions ∧
      marks.refuses lts config.1 negative = true ∧
      ∃ assignment, assignment ∈ assignments lts config.2 ∧
        assignmentWellFormed assignment = true ∧
        let branches := assignmentBranches (competitorsOf lts config.2) assignment
        branchesRequirement negative branches = capability ∧
          negativeAssignmentValid lts (competitorsOf lts config.2) negative assignment = true ∧
          ∀ branch, branch ∈ branches →
            ∃ successor, successor ∈ lts.next config.1 branch.action ∧
              ∃ childCapability,
                ((successor, shift lts branch.competitors branch.action), childCapability) ∈ marked ∧
                  capLe childCapability branch.capability

/-- Executable marking is exactly the order-independent proof-facing marker relation. -/
lemma marks_iff_marksSet
    (lts : CCS.FiniteLTS Action State)
    (marked : CapabilityTable State)
    (config : ReadyConfig State)
    (capability : Capability) :
    marks lts marked config capability = true ↔
      marksSet lts (marked.toFinset : Set (CapabilityConfig State)) config capability := by
  simp [marks, marksSet, branchesValid_iff, and_assoc]

/-- Ready marking is monotone in the set of previously marked child configurations. -/
lemma marksSet_mono
    (lts : CCS.FiniteLTS Action State)
    {left right : Set (CapabilityConfig State)}
    (hSubset : left ⊆ right)
    (config : ReadyConfig State)
    (capability : Capability) :
    marksSet lts left config capability → marksSet lts right config capability := by
  intro hMarks
  rcases hMarks with hBase | ⟨negative, hNegative, hRefuses, assignment, hAssignment,
    hWellFormed, hRequirement, hNegativeValid, hBranches⟩
  · exact Or.inl hBase
  · refine Or.inr ⟨negative, hNegative, hRefuses, assignment, hAssignment, hWellFormed,
      hRequirement, hNegativeValid, ?_⟩
    intro branch hBranch
    rcases hBranches branch hBranch with ⟨successor, hSuccessor, childCapability,
      hChild, hCapability⟩
    exact ⟨successor, hSuccessor, childCapability, hSubset hChild, hCapability⟩

/-- The Mathlib least fixed point of the query-local Ready marker relation. -/
def capabilityTableLfp
    (lts : CCS.FiniteLTS Action State)
    (state : State)
    (competitors : StateSet State) : Set (CapabilityConfig State) :=
  tableLfp
    ((capabilityConfigs (queryConfigs lts state competitors)).toFinset : Set (CapabilityConfig State))
    (fun marked entry => marksSet lts marked entry.1 entry.2)
    (fun hSubset config hMarks => marksSet_mono lts hSubset config.1 config.2 hMarks)

/-- The bounded Ready evaluator computes the Mathlib least marker table. -/
theorem capabilityTable_eq_capabilityTableLfp
    (lts : CCS.FiniteLTS Action State)
    (state : State)
    (competitors : StateSet State) :
    ((capabilityTable lts state competitors).toFinset : Set (CapabilityConfig State)) =
      capabilityTableLfp lts state competitors := by
  let configs := capabilityConfigs (queryConfigs lts state competitors)
  have hTable := saturate_toFinset_eq_tableLfp configs capabilityConfigMem
    (fun marked config => marks lts marked config.1 config.2)
    (fun marked entry => marksSet lts marked entry.1 entry.2)
    (by
      intro config marked
      exact capabilityConfigMem_iff config marked)
    (by
      intro marked config
      exact marks_iff_marksSet lts marked config.1 config.2)
    (by
      intro left right hSubset config hMarks
      exact marksSet_mono lts hSubset config.1 config.2 hMarks)
  simpa only [capabilityTable, capabilityTableLfp, configs] using hTable

/-- Executable capability pruning is semantic minimality over the raw marker table. -/
lemma mem_minimalCapabilities_iff
    (marked : CapabilityTable State)
    (config : ReadyConfig State)
    (capability : Capability) :
    capability ∈ minimalCapabilities marked config ↔
      minimalCap (fun candidate => (config, candidate) ∈ marked) capability := by
  cases capability <;>
    simp [minimalCapabilities, capabilities, capabilityConfigMem_iff,
      capabilityConfigMem_eq_false_iff, capLeBool, minimalCap]
  · intro _ candidate _ hCandidate
    cases candidate <;> simp [capLe] at hCandidate ⊢
  · intro _
    constructor
    · intro hNoT candidate hCandidate hLe
      cases candidate with
      | T => exact False.elim (hNoT hCandidate)
      | S => exact capLe_refl .S
      | F => cases hLe
      | RS => cases hLe
    · intro hMinimal hT
      exact hMinimal .T hT (by simp [capLe])
  · intro _
    constructor
    · intro hNoT candidate hCandidate hLe
      cases candidate with
      | T => exact False.elim (hNoT hCandidate)
      | S => cases hLe
      | F => exact capLe_refl .F
      | RS => cases hLe
    · intro hMinimal hT
      exact hMinimal .T hT (by simp [capLe])
  · intro _
    constructor
    · rintro ⟨hNoT, hNoS, hNoF⟩ candidate hCandidate hLe
      cases candidate with
      | T => exact False.elim (hNoT hCandidate)
      | S => exact False.elim (hNoS hCandidate)
      | F => exact False.elim (hNoF hCandidate)
      | RS => exact capLe_refl .RS
    · intro hMinimal
      refine ⟨?_, ?_, ?_⟩
      · intro hT
        exact hMinimal .T hT (by simp [capLe])
      · intro hS
        exact hMinimal .S hS (by simp [capLe])
      · intro hF
        exact hMinimal .F hF (by simp [capLe])

/--
Certificate that the finite symbolic evaluator computes the exact minimal
capability antichain of `lfpDRSAbsExactCanon` on the listed finite fragment.
-/
structure ReadyCapabilitiesCorrect
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name) : Prop where
  realizes : CCS.FiniteLTS.Realizes lts env decode
  correct : ∀ (state : State) (competitors : StateSet State) (capability : Capability)
    (_ : state ∈ lts.states)
    (_ : ∀ competitor, competitor ∈ competitors → competitor ∈ lts.states),
    capability ∈ readyCapabilities lts state competitors ↔
      lfpDRSAbsExactCanon env (decode state)
        (CCS.FiniteLTS.decodeSet decode competitors) capability

/-- Generic pointwise connection from a certified finite evaluator to the exact Ready lfp. -/
theorem readyCapabilities_correct
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (certificate : ReadyCapabilitiesCorrect lts env decode)
    (state : State)
    (competitors : StateSet State)
    (capability : Capability)
    (hState : state ∈ lts.states)
    (hCompetitors : ∀ competitor, competitor ∈ competitors → competitor ∈ lts.states) :
    capability ∈ readyCapabilities lts state competitors ↔
      lfpDRSAbsExactCanon env (decode state)
        (CCS.FiniteLTS.decodeSet decode competitors) capability := by
  exact certificate.correct state competitors capability hState hCompetitors

/-- A certified finite threshold query is equivalent to semantic Ready failure. -/
theorem failsAt_correct
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (certificate : ReadyCapabilitiesCorrect lts env decode)
    (threshold : Capability)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : ∀ competitor, competitor ∈ competitors → competitor ∈ lts.states) :
    failsAt lts threshold state competitors = true ↔
      abstractFailsAt (lfpDRSAbsExactCanon env) threshold (decode state)
        (CCS.FiniteLTS.decodeSet decode competitors) := by
  constructor
  · intro hFails
    simp only [failsAt, List.any_eq_true] at hFails
    rcases hFails with ⟨capability, hMember, hLe⟩
    exact ⟨capability,
      (readyCapabilities_correct lts env decode certificate state competitors capability
        hState hCompetitors).mp hMember,
      (capLeBool_iff capability threshold).mp hLe⟩
  · rintro ⟨capability, hCapability, hLe⟩
    apply List.any_eq_true.mpr
    exact ⟨capability,
      (readyCapabilities_correct lts env decode certificate state competitors capability
        hState hCompetitors).mpr hCapability,
      (capLeBool_iff capability threshold).mpr hLe⟩

end FiniteLTS
end EqCheckingAbstractInterpretation.Ready
