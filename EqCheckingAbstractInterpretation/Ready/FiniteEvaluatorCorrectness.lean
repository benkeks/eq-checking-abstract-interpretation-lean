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

/-- Every enumerated positive branch contributes its derivative configuration. -/
lemma mem_configSuccessors
    (lts : CCS.FiniteLTS Action State)
    (config : ReadyConfig State)
    (selected : StateSet State)
    (action : Action)
    (target : State)
    (hSelected : selected ∈ powerset (competitorsOf lts config.2))
    (hAction : action ∈ lts.actions)
    (hTarget : target ∈ lts.next config.1 action) :
    (target, shift lts selected action) ∈ configSuccessors lts config := by
  rw [configSuccessors, List.mem_flatMap]
  refine ⟨selected, hSelected, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨action, hAction, ?_⟩
  rw [List.mem_map]
  exact ⟨target, hTarget, rfl⟩

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

        omit [DecidableEq Action] in
        /-- The negative partition never introduces competitors outside its source list. -/
        lemma negativeCompetitors_subset
          (competitors : List State)
          (assignment : Assignment Action) :
          (negativeCompetitors competitors assignment).toFinset ⊆ competitors.toFinset := by
          induction competitors generalizing assignment with
          | nil => simp [negativeCompetitors]
          | cons competitor competitors ih =>
            cases assignment with
            | nil => simp [negativeCompetitors]
            | cons choice assignment =>
                cases choice with
                | none => simp [negativeCompetitors, ih]
                | some value =>
                    intro entry hEntry
                    have hTail : entry ∈ competitors.toFinset :=
                      ih assignment (by simpa [negativeCompetitors] using hEntry)
                    simpa using
                      (Finset.mem_insert.mpr (Or.inr hTail) : entry ∈ insert competitor competitors.toFinset)

        /-- Every negative-partition competitor enables one selected negative action. -/
        lemma negativeCompetitors_enabled
          (lts : CCS.FiniteLTS Action State)
          (negative : List Action)
          (competitors : List State)
          (assignment : Assignment Action)
          (hValid : List.Forall₂ (NegativeAssignmentCondition lts negative) competitors assignment)
          (competitor : State)
          (hCompetitor : competitor ∈ negativeCompetitors competitors assignment) :
          ∃ action, action ∈ negative ∧ (lts.next competitor action).isEmpty = false := by
          induction competitors generalizing assignment competitor with
          | nil =>
            simp [negativeCompetitors] at hCompetitor
          | cons head tail ih =>
            cases assignment with
            | nil => simp [negativeCompetitors] at hCompetitor
            | cons choice assignment =>
              cases hValid with
              | cons hHead hTail =>
                cases choice with
                | none =>
                  simp only [negativeCompetitors, List.mem_cons] at hCompetitor
                  rcases hCompetitor with rfl | hCompetitor
                  · exact hHead rfl
                  · exact ih assignment hTail competitor hCompetitor
                | some value =>
                  simp only [negativeCompetitors] at hCompetitor
                  exact ih assignment hTail competitor hCompetitor

omit [DecidableEq Action] in
/-- Every competitor in an inserted branch comes from the new entry or a prior branch. -/
lemma mem_branchInsert_competitors
    (slot : Nat)
    (action : Action)
    (capability : Capability)
    (competitor : State)
    (branches : List (Branch Action State))
    (branch : Branch Action State)
    (member : State)
    (hBranch : branch ∈ branchInsert slot action capability competitor branches)
    (hMember : member ∈ branch.competitors) :
    member = competitor ∨
      ∃ prior, prior ∈ branches ∧ member ∈ prior.competitors := by
  induction branches generalizing branch with
  | nil =>
      simp [branchInsert] at hBranch
      subst branch
      simp at hMember
      exact Or.inl hMember
  | cons current remaining ih =>
      unfold branchInsert at hBranch
      split at hBranch
      · simp only [List.mem_cons] at hBranch
        rcases hBranch with hBranch | hBranch
        · subst branch
          simp only [Finset.mem_insert] at hMember
          rcases hMember with hMember | hMember
          · exact Or.inl hMember
          · exact Or.inr ⟨current, by simp, hMember⟩
        · exact Or.inr ⟨branch, by simp [hBranch], hMember⟩
      · simp only [List.mem_cons] at hBranch
        rcases hBranch with hBranch | hBranch
        · subst branch
          exact Or.inr ⟨current, by simp, hMember⟩
        · rcases ih branch hBranch hMember with hMember | ⟨prior, hPrior, hPriorMember⟩
          · exact Or.inl hMember
          · exact Or.inr ⟨prior, by simp [hPrior], hPriorMember⟩

omit [DecidableEq Action] in
/-- An inserted branch keeps either the new label or the label of a prior branch. -/
lemma mem_branchInsert_label
    (slot : Nat)
    (action : Action)
    (capability : Capability)
    (competitor : State)
    (branches : List (Branch Action State))
    (branch : Branch Action State)
    (hBranch : branch ∈ branchInsert slot action capability competitor branches) :
    (branch.slot = slot ∧ branch.action = action ∧ branch.capability = capability) ∨
      ∃ prior, prior ∈ branches ∧ branch.slot = prior.slot ∧
        branch.action = prior.action ∧ branch.capability = prior.capability := by
  induction branches generalizing branch with
  | nil =>
      simp [branchInsert] at hBranch
      subst branch
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | cons current remaining ih =>
      unfold branchInsert at hBranch
      split at hBranch
      · simp only [List.mem_cons] at hBranch
        rcases hBranch with hBranch | hBranch
        · subst branch
          exact Or.inr ⟨current, by simp, rfl, rfl, rfl⟩
        · exact Or.inr ⟨branch, by simp [hBranch], rfl, rfl, rfl⟩
      · simp only [List.mem_cons] at hBranch
        rcases hBranch with hBranch | hBranch
        · subst branch
          exact Or.inr ⟨current, by simp, rfl, rfl, rfl⟩
        · rcases ih branch hBranch with hLabel | ⟨prior, hPrior, hSlot, hAction, hCapability⟩
          · exact Or.inl hLabel
          · exact Or.inr ⟨prior, by simp [hPrior], hSlot, hAction, hCapability⟩

omit [DecidableEq Action] in
/-- Grouped positive branches contain only competitors from their aligned source list. -/
lemma assignmentBranches_competitors_subset
    (competitors : List State)
    (assignment : Assignment Action)
    (branch : Branch Action State)
    (member : State)
    (hBranch : branch ∈ assignmentBranches competitors assignment)
    (hMember : member ∈ branch.competitors) :
    member ∈ competitors := by
  induction competitors generalizing assignment branch with
  | nil =>
      cases assignment <;> simp [assignmentBranches] at hBranch
  | cons competitor competitors ih =>
      cases assignment with
      | nil => simp [assignmentBranches] at hBranch
      | cons choice assignment =>
          cases choice with
          | none =>
              exact List.mem_cons.mpr (Or.inr
                (ih assignment branch (by simpa [assignmentBranches] using hBranch) hMember))
          | some choice =>
              rcases choice with ⟨slot, action, capability⟩
              rcases mem_branchInsert_competitors slot action capability competitor
                (assignmentBranches competitors assignment) branch member hBranch hMember with
                hMember | ⟨prior, hPrior, hPriorMember⟩
              · exact List.mem_cons.mpr (Or.inl hMember)
              · exact List.mem_cons.mpr (Or.inr (ih assignment prior hPrior hPriorMember))

omit [DecidableEq Action] in
/-- Every grouped branch label originates in a positive assignment entry. -/
lemma assignmentBranches_label_origin
    (competitors : List State)
    (assignment : Assignment Action)
    (branch : Branch Action State)
    (hBranch : branch ∈ assignmentBranches competitors assignment) :
    some (branch.slot, branch.action, branch.capability) ∈ assignment := by
  induction competitors generalizing assignment branch with
  | nil =>
      cases assignment <;> simp [assignmentBranches] at hBranch
  | cons competitor competitors ih =>
      cases assignment with
      | nil => simp [assignmentBranches] at hBranch
      | cons choice assignment =>
          cases choice with
          | none =>
              exact List.mem_cons.mpr (Or.inr
                (ih assignment branch (by simpa [assignmentBranches] using hBranch)))
          | some choice =>
              rcases choice with ⟨slot, action, capability⟩
              rcases mem_branchInsert_label slot action capability competitor
                (assignmentBranches competitors assignment) branch hBranch with
                hLabel | ⟨prior, hPrior, hSlot, hAction, hCapability⟩
              · rcases hLabel with ⟨hSlot, hAction, hCapability⟩
                simp [hSlot, hAction, hCapability]
              · apply List.mem_cons.mpr
                right
                simpa [hSlot, hAction, hCapability] using ih assignment prior hPrior

/-- A well-formed assignment gives every branch the unique label for its slot. -/
lemma assignmentBranches_label_consistent
    (competitors : List State)
    (assignment : Assignment Action)
    (hWellFormed : assignmentWellFormed assignment = true)
    (branch : Branch Action State)
    (hBranch : branch ∈ assignmentBranches competitors assignment)
    (slot : Nat)
    (action : Action)
    (capability : Capability)
    (hEntry : some (slot, action, capability) ∈ assignment)
    (hSlot : slot = branch.slot) :
    action = branch.action ∧ capability = branch.capability := by
  exact assignmentWellFormed_sound assignment hWellFormed slot branch.slot action branch.action
    capability branch.capability hEntry (assignmentBranches_label_origin competitors assignment branch hBranch) hSlot

omit [DecidableEq Action] in
/-- Inserting a positive assignment covers its competitor with a branch of that label. -/
lemma branchInsert_covers_competitor
    (slot : Nat)
    (action : Action)
    (capability : Capability)
    (competitor : State)
    (branches : List (Branch Action State))
    (hLabels : ∀ branch, branch ∈ branches → branch.slot = slot →
      action = branch.action ∧ capability = branch.capability) :
    ∃ branch, branch ∈ branchInsert slot action capability competitor branches ∧
      branch.slot = slot ∧ branch.action = action ∧ branch.capability = capability ∧
        competitor ∈ branch.competitors := by
  induction branches with
  | nil =>
      refine ⟨{ slot, action, capability, competitors := {competitor} }, by simp [branchInsert],
        rfl, rfl, rfl, by simp⟩
  | cons current remaining ih =>
      unfold branchInsert
      split <;> rename_i hSlot
      · have hInsertedSlot : slot = current.slot := by simpa using hSlot
        have hCurrentSlot : current.slot = slot := hInsertedSlot.symm
        rcases hLabels current (by simp) hCurrentSlot with ⟨hAction, hCapability⟩
        refine ⟨{ current with competitors := insert competitor current.competitors }, by simp,
          hCurrentSlot, ?_, ?_, by simp⟩
        · exact hAction.symm
        · exact hCapability.symm
      · rcases ih (fun branch hBranch hSlot => hLabels branch (by simp [hBranch]) hSlot) with
          ⟨branch, hBranch, hSlot, hAction, hCapability, hCompetitor⟩
        exact ⟨branch, by simp [hBranch], hSlot, hAction, hCapability, hCompetitor⟩

omit [DecidableEq Action] in
/-- Adding a competitor preserves each prior branch's label and members. -/
lemma branchInsert_preserves_member
    (slot : Nat) (action : Action) (capability : Capability) (competitor : State)
    (branches : List (Branch Action State)) :
    ∀ source ∈ branches, ∀ member ∈ source.competitors,
      ∃ updated ∈ branchInsert slot action capability competitor branches,
        updated.slot = source.slot ∧ updated.action = source.action ∧
          updated.capability = source.capability ∧ member ∈ updated.competitors := by
  induction branches with
  | nil => simp
  | cons current remaining ih =>
      intro source hSource member hMember
      simp only [List.mem_cons] at hSource
      unfold branchInsert
      split
      · rcases hSource with rfl | hSource
        · exact ⟨{ source with competitors := insert competitor source.competitors },
            by simp, rfl, rfl, rfl, Finset.mem_insert.mpr (Or.inr hMember)⟩
        · exact ⟨source, by simp [hSource], rfl, rfl, rfl, hMember⟩
      · rcases hSource with rfl | hSource
        · exact ⟨source, by simp, rfl, rfl, rfl, hMember⟩
        · rcases ih source hSource member hMember with
            ⟨updated, hUpdated, hSlot, hAction, hCapability, hUpdatedMember⟩
          exact ⟨updated, by simp [hUpdated], hSlot, hAction, hCapability, hUpdatedMember⟩

/-- Every positive choice in an aligned assignment occurs in its grouped branch. -/
lemma assignmentBranches_cover_positive
    (competitors : List State) (assignment : Assignment Action)
    (hLength : assignment.length = competitors.length)
    (hWellFormed : assignmentWellFormed assignment = true) :
    List.Forall₂
      (fun competitor choice =>
        ∀ slot action capability, choice = some (slot, action, capability) →
          ∃ branch ∈ assignmentBranches competitors assignment,
            branch.slot = slot ∧ branch.action = action ∧ branch.capability = capability ∧
              competitor ∈ branch.competitors)
      competitors assignment := by
  induction competitors generalizing assignment with
  | nil =>
      cases assignment with
      | nil => exact List.Forall₂.nil
      | cons choice assignment => simp at hLength
  | cons competitor competitors ih =>
      cases assignment with
      | nil => simp at hLength
      | cons choice assignment =>
          have hTailLength : assignment.length = competitors.length := by simpa using hLength
          cases choice with
          | none =>
              simp only [assignmentWellFormed] at hWellFormed
              refine List.Forall₂.cons (by simp) ?_
              simpa only [assignmentBranches] using ih assignment hTailLength hWellFormed
          | some choice =>
              rcases choice with ⟨slot, action, capability⟩
              have hWhole := hWellFormed
              simp only [assignmentWellFormed, Bool.and_eq_true] at hWellFormed
              refine List.Forall₂.cons ?_ ?_
              · intro otherSlot otherAction otherCapability hChoice
                cases hChoice
                apply branchInsert_covers_competitor slot action capability competitor
                intro branch hBranch hSlot
                exact assignmentWellFormed_sound (some (slot, action, capability) :: assignment)
                  hWhole slot branch.slot action branch.action capability branch.capability
                  (by simp) (by simp [assignmentBranches_label_origin competitors assignment branch hBranch])
                  hSlot.symm
              · have hTail := ih assignment hTailLength hWellFormed.2
                refine hTail.imp ?_
                intro tailCompetitor tailChoice hTailCoverage tailSlot tailAction
                  tailCapability hTailChoice
                rcases hTailCoverage tailSlot tailAction tailCapability hTailChoice with
                  ⟨source, hSource, hSlot, hAction, hCapability, hMember⟩
                rcases branchInsert_preserves_member slot action capability competitor
                  (assignmentBranches competitors assignment) source hSource tailCompetitor hMember with
                  ⟨updated, hUpdated, hUpdatedSlot, hUpdatedAction, hUpdatedCapability, hUpdatedMember⟩
                exact ⟨updated, hUpdated, hUpdatedSlot.trans hSlot,
                  hUpdatedAction.trans hAction, hUpdatedCapability.trans hCapability, hUpdatedMember⟩

/-- An aligned assignment partitions its competitors into negative and positive groups. -/
lemma assignmentBranches_partition
    (competitors : List State) (assignment : Assignment Action)
    (hLength : assignment.length = competitors.length)
    (hWellFormed : assignmentWellFormed assignment = true)
    (member : State) (hMember : member ∈ competitors) :
    member ∈ negativeCompetitors competitors assignment ∨
      ∃ branch ∈ assignmentBranches competitors assignment, member ∈ branch.competitors := by
  induction competitors generalizing assignment with
  | nil => simp at hMember
  | cons competitor competitors ih =>
      cases assignment with
      | nil => simp at hLength
      | cons choice assignment =>
          have hTailLength : assignment.length = competitors.length := by simpa using hLength
          cases choice with
          | none =>
              simp only [assignmentWellFormed] at hWellFormed
              rcases List.mem_cons.mp hMember with rfl | hMember
              · exact Or.inl (by simp [negativeCompetitors])
              · rcases ih assignment hTailLength hWellFormed hMember with
                  hNegative | ⟨branch, hBranch, hBranchMember⟩
                · exact Or.inl (by simp [negativeCompetitors, hNegative])
                · exact Or.inr ⟨branch, by simpa [assignmentBranches] using hBranch,
                    hBranchMember⟩
          | some choice =>
              rcases choice with ⟨slot, action, capability⟩
              have hTailWellFormed : assignmentWellFormed assignment = true := by
                simp only [assignmentWellFormed, Bool.and_eq_true] at hWellFormed
                exact hWellFormed.2
              rcases List.mem_cons.mp hMember with rfl | hMember
              · have hCovered := assignmentBranches_cover_positive
                  (member :: competitors) (some (slot, action, capability) :: assignment)
                  hLength hWellFormed
                cases hCovered with
                | cons hHead _ =>
                    rcases hHead slot action capability rfl with
                      ⟨branch, hBranch, _, _, _, hBranchMember⟩
                    exact Or.inr ⟨branch, hBranch, hBranchMember⟩
              · rcases ih assignment hTailLength hTailWellFormed hMember with
                  hNegative | ⟨branch, hBranch, hBranchMember⟩
                · exact Or.inl (by simpa [negativeCompetitors] using hNegative)
                · rcases branchInsert_preserves_member slot action capability competitor
                    (assignmentBranches competitors assignment) branch hBranch member hBranchMember with
                    ⟨updated, hUpdated, _, _, _, hUpdatedMember⟩
                  exact Or.inr ⟨updated, by simpa [assignmentBranches] using hUpdated,
                    hUpdatedMember⟩

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

/-- Finite assignment groups provide the refusal, enabledness, and cover premises of a DRS node. -/
lemma assignment_to_DRS_partition
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State) (competitors : StateSet State)
    (negative : List Action) (assignment : Assignment Action)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset)
    (hAssignment : assignment ∈ assignments lts competitors)
    (hWellFormed : assignmentWellFormed assignment = true)
    (hValid : negativeAssignmentValid lts (competitorsOf lts competitors) negative assignment = true)
    (hRefuses : marks.refuses lts state negative = true) :
    let branches := assignmentBranches (competitorsOf lts competitors) assignment
    ∃ Qneg : ProcSet Action Name, ∃ Qpos : Fin branches.length → ProcSet Action Name,
      (∀ action, action ∈ negative → ¬ Enabled env (decode state) action) ∧
      (∀ process, Qneg process → ∃ action, action ∈ negative ∧ Enabled env process action) ∧
      (∀ process, CCS.FiniteLTS.decodeSet decode competitors process →
        Qneg process ∨ ∃ i, Qpos i process) ∧
      (∀ i, Qpos i = CCS.FiniteLTS.decodeSet decode (branches.get i).competitors) := by
  dsimp only
  let listed := competitorsOf lts competitors
  let branches := assignmentBranches listed assignment
  let negativeSet := (negativeCompetitors listed assignment).toFinset
  refine ⟨CCS.FiniteLTS.decodeSet decode negativeSet,
    (fun i => CCS.FiniteLTS.decodeSet decode (branches.get i).competitors),
    (refuses_iff lts env decode realizes state negative hState).mp hRefuses, ?_, ?_, ?_⟩
  · intro process hNegative
    rcases hNegative with ⟨source, hSource, rfl⟩
    have hSourceListed : source ∈ listed := by
      simpa using
      (negativeCompetitors_subset (Action := Action) listed assignment)
        (by simpa [negativeSet] using hSource)
    have hListed : source ∈ lts.states :=
      ((mem_competitorsOf_iff lts competitors source).mp
        (by simpa [listed] using hSourceListed)).1
    rcases negativeCompetitors_enabled lts negative listed assignment
      ((negativeAssignmentValid_iff lts listed negative assignment).mp hValid)
      source (by simpa [negativeSet, listed] using hSource) with
      ⟨action, hAction, hNonempty⟩
    refine ⟨action, hAction, ?_⟩
    by_contra hDisabled
    have hEmpty := (next_isEmpty_iff_not_enabled lts env decode realizes source action hListed).mpr
      hDisabled
    simp [hEmpty] at hNonempty
  · intro process hProcess
    rcases hProcess with ⟨source, hSource, rfl⟩
    have hListed : source ∈ listed :=
      (mem_competitorsOf_iff lts competitors source).mpr
        ⟨by simpa using hCompetitors hSource, hSource⟩
    have hLength := (mem_assignments_iff lts competitors assignment).mp hAssignment |>.1
    rcases assignmentBranches_partition listed assignment hLength hWellFormed source hListed with
      hNegative | ⟨branch, hBranch, hBranchMember⟩
    · exact Or.inl ⟨source, by simpa [negativeSet] using hNegative, rfl⟩
    · rcases List.mem_iff_get.mp hBranch with ⟨i, hBranchEq⟩
      exact Or.inr ⟨i, source, by simpa only [← hBranchEq] using hBranchMember, rfl⟩
  · intro i
    rfl

omit [DecidableEq Action] in
/-- The terminal Ready observation belongs to the concrete lfp over an empty competitor set. -/
lemma lfpDRS_tt_of_empty
    (env : Env Action Name)
    (process : CCS Action Name) :
    lfpDRS env process (fun _ => False) .tt := by
  apply lfpDRS_prefixpoint
  simp [DRS]

omit [DecidableEq Action] in
/-- An empty finite competitor set is semantically witnessed by raw capability `T`. -/
lemma empty_competitors_raw_sound
    {Name : Type w}
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (state : State) :
    alphaCapRaw rsObsCap
      (lfpDRS env (decode state) (CCS.FiniteLTS.decodeSet decode (∅ : StateSet State))) .T := by
  have hDecodeEmpty : CCS.FiniteLTS.decodeSet decode (∅ : StateSet State) = fun _ => False := by
    funext process
    apply propext
    constructor
    · rintro ⟨source, hSource, _⟩
      simp at hSource
    · exact False.elim
  rw [hDecodeEmpty]
  refine ⟨.tt, lfpDRS_tt_of_empty env (decode state), ?_⟩
  simp [rsObsCap, reqOfObs, capLe]

omit [DecidableEq Action] in
/-- A concrete lfp Ready observation witnesses every capability above its requirement. -/
lemma raw_sound_of_lfpDRS
    (env : Env Action Name)
    (process : CCS Action Name)
    (competitors : ProcSet Action Name)
    (observation : RSObs Action)
    (capability : Capability)
    (hObservation : lfpDRS env process competitors observation)
    (hCapability : capLe (reqOfObs observation) capability) :
    alphaCapRaw rsObsCap (lfpDRS env process competitors) capability :=
  ⟨observation, hObservation, hCapability⟩

omit [DecidableEq Action] in
/-- The empty-competitor finite marking rule is sound for the raw Ready abstraction. -/
lemma empty_mark_raw_sound
    {Name : Type w}
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (config : ReadyConfig State)
    (capability : Capability)
    (hEmpty : config.2 = ∅)
    (hCapability : capability = .T) :
    alphaCapRaw rsObsCap
      (lfpDRS env (decode config.1) (CCS.FiniteLTS.decodeSet decode config.2)) capability := by
  rcases config with ⟨state, competitors⟩
  change competitors = ∅ at hEmpty
  change alphaCapRaw rsObsCap
    (lfpDRS env (decode state) (CCS.FiniteLTS.decodeSet decode competitors)) capability
  subst competitors
  subst capability
  exact empty_competitors_raw_sound env decode _

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

/-- Folding configuration expansion never removes an already present configuration. -/
lemma mem_foldl_expand_of_mem
    (lts : CCS.FiniteLTS Action State)
    (drivers initial : List (ReadyConfig State))
    (entry : ReadyConfig State)
    (hEntry : entry ∈ initial) :
    entry ∈ drivers.foldl
      (fun closure config => configUnion (configSuccessors lts config) closure) initial := by
  induction drivers generalizing initial with
  | nil => simpa
  | cons config drivers ih =>
      apply ih
      exact (mem_configUnion_iff entry (configSuccessors lts config) initial).mpr (Or.inr hEntry)

/-- One expansion keeps every seed configuration. -/
lemma mem_expandConfigs_of_mem
    (lts : CCS.FiniteLTS Action State)
    (configs : List (ReadyConfig State))
    (entry : ReadyConfig State)
    (hEntry : entry ∈ configs) :
    entry ∈ expandConfigs lts configs := by
  exact mem_foldl_expand_of_mem lts configs configs entry hEntry

/-- Folding expansion includes direct successors of any configuration it visits. -/
lemma mem_foldl_expand_of_successor
    (lts : CCS.FiniteLTS Action State)
    (drivers initial : List (ReadyConfig State))
    (config entry : ReadyConfig State)
    (hConfig : config ∈ drivers)
    (hSuccessor : entry ∈ configSuccessors lts config) :
    entry ∈ drivers.foldl
      (fun closure config => configUnion (configSuccessors lts config) closure) initial := by
  induction drivers generalizing initial config entry with
  | nil => simp at hConfig
  | cons head tail ih =>
      simp only [List.mem_cons] at hConfig
      cases hConfig with
      | inl hEqual =>
          subst head
          apply mem_foldl_expand_of_mem lts tail
            (configUnion (configSuccessors lts config) initial) entry
          exact (mem_configUnion_iff entry (configSuccessors lts config) initial).mpr
            (Or.inl hSuccessor)
      | inr hTail =>
          exact ih (configUnion (configSuccessors lts head) initial) config entry hTail hSuccessor

/-- One expansion includes every direct successor of one of its seeds. -/
lemma mem_expandConfigs_of_successor
    (lts : CCS.FiniteLTS Action State)
    (configs : List (ReadyConfig State))
    (config entry : ReadyConfig State)
    (hConfig : config ∈ configs)
    (hSuccessor : entry ∈ configSuccessors lts config) :
    entry ∈ expandConfigs lts configs := by
  exact mem_foldl_expand_of_successor lts configs configs config entry hConfig hSuccessor

/-- Repeated configuration expansion preserves every member of its initial seed list. -/
lemma mem_foldl_expandConfigs_of_mem
    (lts : CCS.FiniteLTS Action State)
    (rounds : List Unit)
    (initial : List (ReadyConfig State))
    (entry : ReadyConfig State)
    (hEntry : entry ∈ initial) :
    entry ∈ rounds.foldl (fun configs _ => expandConfigs lts configs) initial := by
  induction rounds generalizing initial with
  | nil => simpa
  | cons _ rounds ih =>
      exact ih (expandConfigs lts initial) (mem_expandConfigs_of_mem lts initial entry hEntry)

/-- Every recursive query expansion round retains its original query configuration. -/
lemma mem_queryConfigsN
    (lts : CCS.FiniteLTS Action State)
    (state : State)
    (competitors : StateSet State)
    (count : Nat) :
    (state, competitors) ∈ queryConfigsN lts state competitors count := by
  induction count with
  | zero => simp [queryConfigsN]
  | succ count ih =>
      exact mem_expandConfigs_of_mem lts (queryConfigsN lts state competitors count)
        (state, competitors) ih

/-- The bounded query domain always contains the queried configuration. -/
lemma mem_queryConfigs
    (lts : CCS.FiniteLTS Action State)
    (state : State)
    (competitors : StateSet State) :
    (state, competitors) ∈ queryConfigs lts state competitors := by
  unfold queryConfigs
  exact mem_queryConfigsN lts state competitors _

/-- Folding expansion preserves containment in the represented configuration universe. -/
lemma foldl_expand_subset_configUniverse
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (drivers initial : List (ReadyConfig State))
    (hDrivers : ∀ config, config ∈ drivers → config ∈ configUniverse lts)
    (hInitial : ∀ config, config ∈ initial → config ∈ configUniverse lts) :
    ∀ config, config ∈ drivers.foldl
      (fun closure config => configUnion (configSuccessors lts config) closure) initial →
        config ∈ configUniverse lts := by
  induction drivers generalizing initial with
  | nil => exact hInitial
  | cons head tail ih =>
      apply ih
      · intro config hConfig
        exact hDrivers config (by simp [hConfig])
      · intro config hConfig
        rcases (mem_configUnion_iff config (configSuccessors lts head) initial).mp hConfig with
          hSuccessor | hOld
        · exact configSuccessors_subset_configUniverse lts env decode realizes head
            (hDrivers head (by simp)) config hSuccessor
        · exact hInitial config hOld

/-- One Ready configuration expansion stays within the represented universe. -/
lemma expandConfigs_subset_configUniverse
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (configs : List (ReadyConfig State))
    (hConfigs : ∀ config, config ∈ configs → config ∈ configUniverse lts) :
    ∀ config, config ∈ expandConfigs lts configs → config ∈ configUniverse lts := by
  exact foldl_expand_subset_configUniverse lts env decode realizes configs configs hConfigs hConfigs

/-- Repeated configuration expansion remains within the represented universe. -/
lemma foldl_expandConfigs_subset_configUniverse
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (rounds : List Unit)
    (initial : List (ReadyConfig State))
    (hInitial : ∀ config, config ∈ initial → config ∈ configUniverse lts) :
    ∀ config, config ∈ rounds.foldl (fun configs _ => expandConfigs lts configs) initial →
      config ∈ configUniverse lts := by
  induction rounds generalizing initial with
  | nil => exact hInitial
  | cons _ rounds ih =>
      apply ih
      exact expandConfigs_subset_configUniverse lts env decode realizes initial hInitial

  /-- Every recursive query expansion round stays inside the represented universe. -/
  lemma queryConfigsN_subset_configUniverse
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    ∀ count config, config ∈ queryConfigsN lts state competitors count → config ∈ configUniverse lts := by
    intro count
    induction count with
    | zero =>
      intro config hConfig
      simp only [queryConfigsN, List.mem_singleton] at hConfig
      subst config
      exact (mem_configUniverse_iff lts state competitors).mpr ⟨hState, hCompetitors⟩
    | succ count ih =>
      intro config hConfig
      apply expandConfigs_subset_configUniverse lts env decode realizes
      · exact ih
      · exact hConfig

/-- The bounded query domain only contains configurations represented by the finite LTS. -/
lemma queryConfigs_subset_configUniverse
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    ∀ config, config ∈ queryConfigs lts state competitors → config ∈ configUniverse lts := by
  unfold queryConfigs
  exact queryConfigsN_subset_configUniverse lts env decode realizes state competitors
    hState hCompetitors _

/-- Proof-facing direct configuration closure used by query-domain expansion. -/
def configStepSet
    (lts : CCS.FiniteLTS Action State)
    (marked : Set (ReadyConfig State))
    (config : ReadyConfig State) : Prop :=
  ∃ source, source ∈ marked ∧ config ∈ configSuccessors lts source

/-- Direct configuration closure is monotone in the already-known configurations. -/
lemma configStepSet_mono
    (lts : CCS.FiniteLTS Action State)
    {left right : Set (ReadyConfig State)}
    (hSubset : left ⊆ right)
    (config : ReadyConfig State) :
    configStepSet lts left config → configStepSet lts right config := by
  rintro ⟨source, hSource, hSuccessor⟩
  exact ⟨source, hSubset hSource, hSuccessor⟩

/-- Configuration closure seeded by the query configuration itself. -/
def queryConfigStepSet
    (lts : CCS.FiniteLTS Action State)
    (seed : ReadyConfig State)
    (marked : Set (ReadyConfig State))
    (config : ReadyConfig State) : Prop :=
  config = seed ∨ configStepSet lts marked config

/-- The seeded configuration closure relation is monotone. -/
lemma queryConfigStepSet_mono
    (lts : CCS.FiniteLTS Action State)
    (seed : ReadyConfig State)
    {left right : Set (ReadyConfig State)}
    (hSubset : left ⊆ right)
    (config : ReadyConfig State) :
    queryConfigStepSet lts seed left config → queryConfigStepSet lts seed right config := by
  intro hStep
  rcases hStep with hSeed | hStep
  · exact Or.inl hSeed
  · exact Or.inr (configStepSet_mono lts hSubset config hStep)

/-- Once the seed is marked, the seeded step is the ordinary successor step. -/
lemma tableStep_queryConfigStepSet_eq_tableStep
    (lts : CCS.FiniteLTS Action State)
    (domain marked : Set (ReadyConfig State))
    (seed : ReadyConfig State)
    (hSeed : seed ∈ marked) :
    tableStep domain (queryConfigStepSet lts seed) marked =
      tableStep domain (configStepSet lts) marked := by
  ext config
  simp only [tableStep, Set.mem_union, Set.mem_setOf_eq, queryConfigStepSet]
  constructor
  · rintro (hMarked | ⟨hDomain, hSeedConfig | hSuccessor⟩)
    · exact Or.inl hMarked
    · exact Or.inl (hSeedConfig ▸ hSeed)
    · exact Or.inr ⟨hDomain, hSuccessor⟩
  · rintro (hMarked | ⟨hDomain, hSuccessor⟩)
    · exact Or.inl hMarked
    · exact Or.inr ⟨hDomain, Or.inr hSuccessor⟩

/-- Folding expansion adds only direct successors of configurations it visits. -/
lemma mem_foldl_expand_iff
    (lts : CCS.FiniteLTS Action State)
    (drivers initial : List (ReadyConfig State))
    (entry : ReadyConfig State) :
    entry ∈ drivers.foldl
      (fun closure config => configUnion (configSuccessors lts config) closure) initial ↔
      entry ∈ initial ∨ ∃ source, source ∈ drivers ∧ entry ∈ configSuccessors lts source := by
  induction drivers generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl]
      rw [ih, mem_configUnion_iff]
      constructor
      · rintro ((hSuccessor | hInitial) | ⟨source, hSource, hSuccessor⟩)
        · exact Or.inr ⟨head, by simp, hSuccessor⟩
        · exact Or.inl hInitial
        · exact Or.inr ⟨source, by simp [hSource], hSuccessor⟩
      · rintro (hInitial | ⟨source, hSource, hSuccessor⟩)
        · exact Or.inl (Or.inr hInitial)
        · simp only [List.mem_cons] at hSource
          rcases hSource with rfl | hSource
          · exact Or.inl (Or.inl hSuccessor)
          · exact Or.inr ⟨source, hSource, hSuccessor⟩

/-- One executable expansion is precisely one proof-facing configuration closure step. -/
lemma expandConfigs_toFinset_eq_tableStep
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (configs : List (ReadyConfig State)) :
    (∀ config, config ∈ configs → config ∈ configUniverse lts) →
    ((expandConfigs lts configs).toFinset : Set (ReadyConfig State)) =
      tableStep (configUniverse lts).toFinset (configStepSet lts)
        (configs.toFinset : Set (ReadyConfig State)) := by
  intro hConfigs
  ext config
  constructor
  · intro hConfig
    have hMembers := (mem_foldl_expand_iff lts configs configs config).mp (by
      simpa [expandConfigs] using hConfig)
    rcases hMembers with hOld | ⟨source, hSource, hSuccessor⟩
    · exact Or.inl (by simpa using hOld)
    · refine Or.inr ⟨?_, source, by simpa using hSource, hSuccessor⟩
      simpa using configSuccessors_subset_configUniverse lts env decode realizes source
        (hConfigs source hSource) config hSuccessor
  · intro hConfig
    rcases hConfig with hOld | ⟨_, source, hSource, hSuccessor⟩
    · exact (by simpa [expandConfigs] using
        mem_expandConfigs_of_mem lts configs config (by simpa using hOld))
    · exact (by simpa [expandConfigs] using
        mem_expandConfigs_of_successor lts configs source config (by simpa using hSource) hSuccessor)

/-- Recursive query expansion is the singleton-seeded generic table iteration. -/
lemma queryConfigsN_toFinset_eq_tableIter
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    ∀ count,
      ((queryConfigsN lts state competitors count).toFinset : Set (ReadyConfig State)) =
        tableIter (configUniverse lts).toFinset
          (queryConfigStepSet lts (state, competitors)) (count + 1) := by
  intro count
  induction count with
  | zero =>
      ext config
      simp only [queryConfigsN, tableIter,
        tableStep, Set.mem_union, Set.mem_empty_iff_false, false_or, Set.mem_setOf_eq,
        queryConfigStepSet, configStepSet]
      constructor
      · intro hConfig
        have hSeed : config = (state, competitors) := by simpa using hConfig
        subst config
        exact ⟨(by simpa using
          (mem_configUniverse_iff lts state competitors).mpr ⟨hState, hCompetitors⟩), Or.inl rfl⟩
      · rintro ⟨_, hSeed | ⟨source, hEmpty, _⟩⟩
        · simp [hSeed]
        · simp at hEmpty
  | succ count ih =>
      rw [queryConfigsN, expandConfigs_toFinset_eq_tableStep lts env decode realizes]
      · rw [ih]
        change tableStep (configUniverse lts).toFinset (configStepSet lts)
            (tableIter (configUniverse lts).toFinset
              (queryConfigStepSet lts (state, competitors)) (count + 1)) =
          tableStep (configUniverse lts).toFinset (queryConfigStepSet lts (state, competitors))
            (tableIter (configUniverse lts).toFinset
              (queryConfigStepSet lts (state, competitors)) (count + 1))
        exact (tableStep_queryConfigStepSet_eq_tableStep lts _ _ (state, competitors) (by
          rw [← ih]
          simpa using mem_queryConfigsN lts state competitors count)).symm
      · exact queryConfigsN_subset_configUniverse lts env decode realizes state competitors
          hState hCompetitors count

/-- The ordered powerset enumerator has the expected binary cardinality. -/
lemma length_powerset (elements : List State) :
    (powerset elements).length = 2 ^ elements.length := by
  induction elements with
  | nil => simp [powerset]
  | cons element elements ih =>
      calc
        (powerset (element :: elements)).length = 2 * (powerset elements).length := by
          simp [powerset, two_mul]
        _ = 2 * 2 ^ elements.length := by rw [ih]
        _ = 2 ^ (element :: elements).length := by simp [Nat.pow_succ, Nat.mul_comm]

/-- Flat-mapping a fixed-length mapped list multiplies the input and output lengths. -/
lemma length_flatMap_map
    {Element Value Result : Type _}
    (elements : List Element)
    (values : List Value)
    (map : Element → Value → Result) :
    (elements.flatMap (fun element => values.map (map element))).length =
      elements.length * values.length := by
  induction elements with
  | nil => simp
  | cons element elements ih =>
      simp [ih, Nat.succ_mul, Nat.add_comm]

/-- The global configuration enumeration has the query expansion bound as its length. -/
lemma length_configUniverse (lts : CCS.FiniteLTS Action State) :
    (configUniverse lts).length = lts.states.length * 2 ^ lts.states.length := by
  unfold configUniverse
  rw [length_flatMap_map]
  exact congrArg (fun length => lts.states.length * length) (length_powerset lts.states)

/-- The represented configuration universe has no more distinct entries than the query bound. -/
lemma card_configUniverse_toFinset_le (lts : CCS.FiniteLTS Action State) :
    (configUniverse lts).toFinset.card ≤ lts.states.length * 2 ^ lts.states.length := by
  rw [← length_configUniverse lts]
  exact List.toFinset_card_le _

/-- The bounded query domain is closed under one Ready configuration successor. -/
lemma queryConfigs_closed
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset)
    (config child : ReadyConfig State)
    (hConfig : config ∈ queryConfigs lts state competitors)
    (hChild : child ∈ configSuccessors lts config) :
    child ∈ queryConfigs lts state competitors := by
  let bound := lts.states.length * 2 ^ lts.states.length
  have hCard : (configUniverse lts).toFinset.card ≤ bound + 1 :=
    Nat.le_trans (card_configUniverse_toFinset_le lts) (Nat.le_succ _)
  have hPrefixed := tableIter_prefixed_of_card_le (configUniverse lts).toFinset
    (queryConfigStepSet lts (state, competitors)) (bound + 1) hCard
  have hQueryIter :
      ((queryConfigs lts state competitors).toFinset : Set (ReadyConfig State)) =
        tableIter (configUniverse lts).toFinset
          (queryConfigStepSet lts (state, competitors)) (bound + 1) := by
    unfold queryConfigs
    exact queryConfigsN_toFinset_eq_tableIter lts env decode realizes state competitors
      hState hCompetitors bound
  have hConfigUniverse : config ∈ configUniverse lts :=
    queryConfigs_subset_configUniverse lts env decode realizes state competitors
      hState hCompetitors config hConfig
  have hChildUniverse : child ∈ configUniverse lts :=
    configSuccessors_subset_configUniverse lts env decode realizes config hConfigUniverse child hChild
  have hChildStep : child ∈ tableStep (configUniverse lts).toFinset
      (queryConfigStepSet lts (state, competitors))
      ((queryConfigs lts state competitors).toFinset : Set (ReadyConfig State)) :=
    Or.inr ⟨by simpa using hChildUniverse, Or.inr ⟨config, by simpa using hConfig, hChild⟩⟩
  rw [hQueryIter] at hChildStep
  have hChildMarked := hPrefixed hChildStep
  rw [← hQueryIter] at hChildMarked
  simpa using hChildMarked

/-- Every enumerated positive branch from a query configuration stays in its query domain. -/
lemma mem_queryConfigs_of_configSuccessor
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset)
    (config : ReadyConfig State)
    (hConfig : config ∈ queryConfigs lts state competitors)
    (selected : StateSet State)
    (action : Action)
    (target : State)
    (hSelected : selected ∈ powerset (competitorsOf lts config.2))
    (hAction : action ∈ lts.actions)
    (hTarget : target ∈ lts.next config.1 action) :
    (target, shift lts selected action) ∈ queryConfigs lts state competitors := by
  apply queryConfigs_closed lts env decode realizes state competitors hState hCompetitors config
    (target, shift lts selected action) hConfig
  exact mem_configSuccessors lts config selected action target hSelected hAction hTarget

omit [DecidableEq State] in
/-- Capability-domain enumeration contains exactly each query configuration at each capability. -/
lemma mem_capabilityConfigs_iff
    (configs : List (ReadyConfig State))
    (config : ReadyConfig State)
    (capability : Capability) :
    (config, capability) ∈ capabilityConfigs configs ↔
      config ∈ configs ∧ capability ∈ capabilities := by
  constructor
  · intro hMember
    rw [capabilityConfigs, List.mem_flatMap] at hMember
    rcases hMember with ⟨source, hSource, hCapability⟩
    rw [List.mem_map] at hCapability
    rcases hCapability with ⟨candidate, hCandidate, hEqual⟩
    cases hEqual
    exact ⟨hSource, hCandidate⟩
  · rintro ⟨hConfig, hCapability⟩
    rw [capabilityConfigs, List.mem_flatMap]
    refine ⟨config, hConfig, ?_⟩
    exact List.mem_map.mpr ⟨capability, hCapability, rfl⟩

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

/-- A finite marking step preserves semantic raw soundness of all child marks. -/
lemma marksSet_raw_sound
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (marked : Set (CapabilityConfig State))
    (hMarked : ∀ config childCapability, (config, childCapability) ∈ marked →
      alphaCapRaw rsObsCap
        (lfpDRS env (decode config.1) (CCS.FiniteLTS.decodeSet decode config.2))
        childCapability)
    (config : ReadyConfig State)
    (capability : Capability)
    (hState : config.1 ∈ lts.states)
    (hCompetitors : config.2 ⊆ lts.states.toFinset)
    (hMarks : marksSet lts marked config capability) :
    alphaCapRaw rsObsCap
      (lfpDRS env (decode config.1) (CCS.FiniteLTS.decodeSet decode config.2)) capability := by
  rcases hMarks with ⟨hEmpty, hCapability⟩ |
    ⟨negative, hNegative, hRefuses, assignment, hAssignment, hWellFormed,
      hRequirement, hValid, hBranches⟩
  · exact empty_mark_raw_sound env decode config capability hEmpty hCapability
  · classical
    let branches := assignmentBranches (competitorsOf lts config.2) assignment
    rcases assignment_to_DRS_partition lts env decode realizes config.1 config.2
      negative assignment hState hCompetitors hAssignment hWellFormed hValid hRefuses with
      ⟨Qneg, Qpos, hRefuse, hEnabled, hCover, hQpos⟩
    have hChildren : ∀ branch, branch ∈ branches →
        ∃ observation : RSObs Action, ∃ successor : State,
          Deriv env (decode config.1) branch.action (decode successor) ∧
          lfpDRS env (decode successor)
            (DerivSetOf env (CCS.FiniteLTS.decodeSet decode branch.competitors)
              branch.action) observation ∧
          capLe (reqOfObs observation) branch.capability := by
      intro branch hBranch
      rcases hBranches branch (by simpa [branches] using hBranch) with
        ⟨successor, hNext, childCapability, hChild, hChildLe⟩
      rcases hMarked (successor, shift lts branch.competitors branch.action)
          childCapability hChild with
        ⟨observation, hObservation, hObservationLe⟩
      have hListed : ∀ source, source ∈ branch.competitors → source ∈ lts.states := by
        intro source hSource
        exact (mem_competitorsOf_iff lts config.2 source).mp
          (assignmentBranches_competitors_subset (competitorsOf lts config.2)
            assignment branch source (by simpa [branches] using hBranch) hSource) |>.1
      have hShift : CCS.FiniteLTS.decodeSet decode
          (shift lts branch.competitors branch.action) =
          DerivSetOf env (CCS.FiniteLTS.decodeSet decode branch.competitors)
            branch.action := by
        funext process
        apply propext
        exact decodeSet_shift_iff lts env decode realizes branch.competitors
          branch.action process hListed
      refine ⟨observation, successor, realizes.next_sound config.1
        branch.action successor hNext, ?_,
        capLe_trans hObservationLe hChildLe⟩
      simpa only [← hShift] using hObservation
    let childObs : Branch Action State → RSObs Action := fun branch =>
      if hBranch : branch ∈ branches then Classical.choose (hChildren branch hBranch) else .tt
    have hChild : ∀ branch, branch ∈ branches →
        ∃ successor : State, Deriv env (decode config.1) branch.action (decode successor) ∧
          lfpDRS env (decode successor)
            (DerivSetOf env (CCS.FiniteLTS.decodeSet decode branch.competitors)
              branch.action) (childObs branch) ∧
          capLe (reqOfObs (childObs branch)) branch.capability := by
      intro branch hBranch
      simpa only [childObs, dif_pos hBranch] using Classical.choose_spec (hChildren branch hBranch)
    let pos := branches.map (fun branch => (branch.action, childObs branch))
    have hPosLength : pos.length = branches.length := by simp [pos]
    have hDRS : DRS env (lfpDRS env) (decode config.1)
        (CCS.FiniteLTS.decodeSet decode config.2) (.node pos negative) := by
      let Qpos' : Fin pos.length → ProcSet Action Name :=
        fun i => Qpos ⟨i.1, by simpa only [hPosLength] using i.2⟩
      refine ⟨Qneg, Qpos', ?_, hRefuse, hEnabled, ?_⟩
      · intro i
        let index : Fin branches.length := ⟨i.1, by simpa only [hPosLength] using i.2⟩
        have hBranch : branches.get index ∈ branches := List.get_mem _ _
        rcases hChild (branches.get index) hBranch with
          ⟨successor, hDeriv, hObservation, _⟩
        refine ⟨decode successor, ?_, ?_⟩
        · simpa [pos, index] using hDeriv
        · have hPosEq := hQpos index
          simpa [pos, index, Qpos', hPosEq] using hObservation
      · intro process hProcess
        rcases hCover process hProcess with hNeg | ⟨i, hPos⟩
        · exact Or.inl hNeg
        · exact Or.inr ⟨⟨i.1, by simpa only [hPosLength] using i.2⟩, hPos⟩
    have hRequirementLe : capLe (reqOfObs (.node pos negative))
        (branchesRequirement negative branches) :=
      reqOfObs_branches_le negative branches childObs
        (fun branch hBranch => (hChild branch hBranch).choose_spec.2.2)
    exact raw_sound_of_lfpDRS env (decode config.1)
      (CCS.FiniteLTS.decodeSet decode config.2) (.node pos negative) capability
      (lfpDRS_prefixpoint env _ _ _ hDRS)
      (capLe_trans hRequirementLe (by simpa [branches] using hRequirement.symm ▸ capLe_refl capability))

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

/-- A valid final-table Ready mark is recorded in the executable capability table. -/
lemma capabilityTable_closed
    (lts : CCS.FiniteLTS Action State)
    (state : State)
    (competitors : StateSet State)
    (config : ReadyConfig State)
    (capability : Capability)
    (hConfig : config ∈ queryConfigs lts state competitors)
    (hCapability : capability ∈ capabilities)
    (hMarks : marks lts (capabilityTable lts state competitors) config capability = true) :
    capabilityConfigMem (config, capability) (capabilityTable lts state competitors) = true := by
  apply (capabilityConfigMem_iff (config, capability) (capabilityTable lts state competitors)).mpr
  have hDomain : (config, capability) ∈
      ((capabilityConfigs (queryConfigs lts state competitors)).toFinset :
        Set (CapabilityConfig State)) := by
    simpa using (mem_capabilityConfigs_iff (queryConfigs lts state competitors) config capability).mpr
      ⟨hConfig, hCapability⟩
  have hMarked : marksSet lts
      ((capabilityTable lts state competitors).toFinset : Set (CapabilityConfig State))
      config capability :=
    (marks_iff_marksSet lts (capabilityTable lts state competitors) config capability).mp hMarks
  rw [capabilityTable_eq_capabilityTableLfp lts state competitors] at hMarked
  have hLfpMember : (config, capability) ∈ capabilityTableLfp lts state competitors := by
    rw [capabilityTableLfp, ← tableStep_tableLfp
      ((capabilityConfigs (queryConfigs lts state competitors)).toFinset : Set (CapabilityConfig State))
      (fun marked entry => marksSet lts marked entry.1 entry.2)
      (fun hSubset entry hEntry =>
        marksSet_mono lts hSubset entry.1 entry.2 hEntry)]
    exact Or.inr ⟨hDomain, hMarked⟩
  rw [← capabilityTable_eq_capabilityTableLfp lts state competitors] at hLfpMember
  simpa using hLfpMember

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

/-- Every entry computed by the finite Ready table has a concrete lfp observation. -/
lemma capabilityTable_raw_sound
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State) (competitors : StateSet State)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset)
    (entry : CapabilityConfig State)
    (hEntry : entry ∈ capabilityTable lts state competitors) :
    alphaCapRaw rsObsCap
      (lfpDRS env (decode entry.1.1) (CCS.FiniteLTS.decodeSet decode entry.1.2)) entry.2 := by
  let semantic : Set (CapabilityConfig State) := fun item =>
    alphaCapRaw rsObsCap
      (lfpDRS env (decode item.1.1) (CCS.FiniteLTS.decodeSet decode item.1.2)) item.2
  have hPrefixed : tableStep
      ((capabilityConfigs (queryConfigs lts state competitors)).toFinset :
        Set (CapabilityConfig State))
      (fun marked item => marksSet lts marked item.1 item.2) semantic ⊆ semantic := by
    intro item hItem
    rcases hItem with hOld | ⟨hDomain, hMarks⟩
    · exact hOld
    · have hConfig : item.1 ∈ queryConfigs lts state competitors :=
        ((mem_capabilityConfigs_iff (queryConfigs lts state competitors) item.1 item.2).mp
          (by simpa using hDomain)).1
      have hRepresented := queryConfigs_subset_configUniverse lts env decode realizes
        state competitors hState hCompetitors item.1 hConfig
      rcases (mem_configUniverse_iff lts item.1.1 item.1.2).mp hRepresented with
        ⟨hItemState, hItemCompetitors⟩
      exact marksSet_raw_sound lts env decode realizes semantic
        (fun config childCapability hChild => hChild) item.1 item.2
        hItemState hItemCompetitors hMarks
  have hLfp : entry ∈ capabilityTableLfp lts state competitors := by
    rw [← capabilityTable_eq_capabilityTableLfp lts state competitors]
    simpa using hEntry
  have hSemantic := tableLfp_subset_of_prefixed
    ((capabilityConfigs (queryConfigs lts state competitors)).toFinset :
      Set (CapabilityConfig State))
    (fun marked item => marksSet lts marked item.1 item.2)
    (fun hSubset item hMarks => marksSet_mono lts hSubset item.1 item.2 hMarks)
    semantic hPrefixed
  exact hSemantic hLfp

omit [DecidableEq Action] in
/-- Filtering an action list selects a member of its list-valued powerset. -/
lemma filter_mem_listPowerset (actions : List Action) (selected : Action → Bool) :
    actions.filter selected ∈ listPowerset actions := by
  induction actions with
  | nil => simp [listPowerset]
  | cons action actions ih =>
      change (action :: actions).filter selected ∈
        listPowerset actions ++ (listPowerset actions).map (action :: ·)
      by_cases hSelected : selected action = true
      · simp [hSelected, ih]
      · simp [hSelected, ih]

/-- Refusal-only semantic steps use the all-negative assignment in the root query table. -/
lemma refusal_only_step_cofinal
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (root : State) (initial : StateSet State)
    (state : State) (competitors : StateSet State) (neg : List Action)
    (hState : state ∈ lts.states)
    (hConfig : (state, competitors) ∈ queryConfigs lts root initial)
    (Q : ProcSet Action Name)
    (hSubset : ∀ process, CCS.FiniteLTS.decodeSet decode competitors process → Q process)
    {ρ : DiffSysRS Action Name (RSObs Action)}
    (hStep : DRS env ρ (decode state) Q (.node [] neg)) :
    ∃ finiteCapability, ((state, competitors), finiteCapability) ∈
        capabilityTable lts root initial ∧
      capLe finiteCapability (reqOfObs (.node [] neg)) := by
  classical
  let listed := competitorsOf lts competitors
  let negative := lts.actions.filter (fun action => decide (action ∈ neg))
  let assignment : Assignment Action := listed.map (fun _ => none)
  rcases hStep with ⟨Qneg, Qpos, _, hRefuse, hEnabled, hCover⟩
  have hNegative : negative ∈ listPowerset lts.actions :=
    filter_mem_listPowerset lts.actions _
  have hRefuses : marks.refuses lts state negative = true :=
    (refuses_iff lts env decode realizes state negative hState).mpr (by
      intro action hAction
      exact hRefuse action (decide_eq_true_eq.mp (List.mem_filter.mp hAction).2))
  have hAssignment : assignment ∈ assignments lts competitors := by
    apply (mem_assignments_iff lts competitors assignment).mpr
    refine ⟨by simp [assignment, listed], ?_⟩
    intro choice hChoice
    have hNone : choice = none := by
      rcases List.mem_map.mp hChoice with ⟨_, _, hEqual⟩
      exact hEqual.symm
    subst choice
    simp [assignmentChoices]
  have hWellFormed : assignmentWellFormed assignment = true := by
    have hForall : ∀ sources : List State,
        assignmentWellFormed (sources.map (fun _ => (none : Option (Nat × Action × Capability)))) =
          true := by
      intro sources
      induction sources with
      | nil => rfl
      | cons source sources ih => simpa only [List.map, assignmentWellFormed] using ih
    exact hForall listed
  have hBranches : assignmentBranches listed assignment = [] := by
    have hForall : ∀ sources : List State,
        assignmentBranches sources
          (sources.map (fun _ => (none : Option (Nat × Action × Capability)))) = [] := by
      intro sources
      induction sources with
      | nil => rfl
      | cons source sources ih => simpa only [List.map, assignmentBranches] using ih
    exact hForall listed
  have hNegativeEnabled : ∀ source, source ∈ listed →
      ∃ action, action ∈ negative ∧ (lts.next source action).isEmpty = false := by
    intro source hSourceListed
    rcases (mem_competitorsOf_iff lts competitors source).mp hSourceListed with
      ⟨hListed, hSource⟩
    rcases hCover (decode source) (hSubset (decode source) ⟨source, hSource, rfl⟩) with
      hQneg | ⟨index, _⟩
    · rcases hEnabled (decode source) hQneg with ⟨action, hAction, hEnabledAction⟩
      refine ⟨action, List.mem_filter.mpr ⟨realizes.action_complete action,
        decide_eq_true_eq.mpr hAction⟩, ?_⟩
      cases hEmpty : (lts.next source action).isEmpty with
      | false => rfl
      | true =>
          have hDisabled :=
            (next_isEmpty_iff_not_enabled lts env decode realizes source action hListed).mp hEmpty
          exact (hDisabled hEnabledAction).elim
    · exact (Nat.not_lt_zero index.val index.isLt).elim
  have hValid : negativeAssignmentValid lts listed negative assignment = true := by
    apply (negativeAssignmentValid_iff lts listed negative assignment).mpr
    change List.Forall₂ (NegativeAssignmentCondition lts negative) listed
      (listed.map (fun _ => none))
    have hForall : ∀ sources : List State,
        (∀ source, source ∈ sources → source ∈ listed) →
          List.Forall₂ (NegativeAssignmentCondition lts negative) sources
            (sources.map (fun _ => none)) := by
      intro sources hSubset
      induction sources with
      | nil => exact List.Forall₂.nil
      | cons source sources ih =>
          apply List.Forall₂.cons ?_ (ih (fun member hMember =>
            hSubset member (by simp [hMember])))
          intro _
          exact hNegativeEnabled source (hSubset source (by simp))
    exact hForall listed (fun _ hMember => hMember)
  have hNegEmpty : negative.isEmpty = neg.isEmpty := by
    cases neg with
    | nil => simp [negative]
    | cons action rest =>
        have hAction : action ∈ negative := by
          simp [negative, realizes.action_complete action]
        have hNonempty : negative.isEmpty = false := by
          cases hList : negative with
          | nil => simp [hList] at hAction
          | cons _ _ => simp
        simpa using hNonempty
  let finiteCapability := branchesRequirement negative ([] : List (Branch Action State))
  have hFiniteEq : finiteCapability = req false (!neg.isEmpty) := by
    cases hEmpty : neg.isEmpty <;>
      simp [finiteCapability, branchesRequirement, branchCapabilities, hNegEmpty, hEmpty,
        req, capJoin]
  have hMark : marksSet lts
      ((capabilityTable lts root initial).toFinset : Set (CapabilityConfig State))
      (state, competitors) finiteCapability := by
    right
    refine ⟨negative, hNegative, hRefuses, assignment, hAssignment, hWellFormed, ?_,
      hValid, ?_⟩
    · simp [finiteCapability, listed, hBranches]
    · simp [listed, hBranches]
  have hMember : ((state, competitors), finiteCapability) ∈
      capabilityTable lts root initial := by
    exact (capabilityConfigMem_iff _ _).mp
      (capabilityTable_closed lts root initial (state, competitors) finiteCapability
        hConfig (by
          rw [hFiniteEq]
          cases neg <;> simp [capabilities, req])
        ((marks_iff_marksSet lts _ (state, competitors) finiteCapability).mpr hMark))
  refine ⟨finiteCapability, hMember, ?_⟩
  rw [hFiniteEq]
  have hRequirement : reqOfObs (.node [] neg) = req false (!neg.isEmpty) := by
    cases neg <;> rfl
  rw [hRequirement]
  exact capLe_refl _

/-- Cofinality at every represented subset in one query-local marker table. -/
def finiteCofinalRelation
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (decode : State → CCS Action Name)
    (root : State) (initial : StateSet State) :
    DiffSysRS Action Name (RSObs Action) :=
  fun process Q observation =>
    ∀ config ∈ queryConfigs lts root initial,
      process = decode config.1 →
      (∀ q, CCS.FiniteLTS.decodeSet decode config.2 q → Q q) →
        ∃ finiteCapability, (config, finiteCapability) ∈ capabilityTable lts root initial ∧
          capLe finiteCapability (reqOfObs observation)

/-- The terminal DRS step is cofinal in a fixed query table. -/
lemma finiteCofinalRelation_tt
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (root : State) (initial : StateSet State)
    (process : CCS Action Name) (Q : ProcSet Action Name)
    (hStep : DRS env (finiteCofinalRelation lts decode root initial) process Q .tt) :
    finiteCofinalRelation lts decode root initial process Q .tt := by
  intro config hConfig hProcess hSubset
  have hEmpty : config.2 = ∅ := by
    ext source
    simp
    intro hSource
    exact hStep (decode source) (hSubset (decode source) ⟨source, hSource, rfl⟩)
  have hMark : marks lts (capabilityTable lts root initial) config .T = true := by
    rcases config with ⟨state, competitors⟩
    change competitors = ∅ at hEmpty
    simp [marks, hEmpty]
  refine ⟨.T, (capabilityConfigMem_iff _ _).mp
    (capabilityTable_closed lts root initial config .T hConfig
      (by simp [capabilities]) hMark), ?_⟩
  simp [capLe]

/-- A semantic child restricted to listed competitors is marked in the root query table. -/
lemma finiteCofinalRelation_child
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (root : State) (initial : StateSet State)
    (hRoot : root ∈ lts.states)
    (hInitial : initial ⊆ lts.states.toFinset)
    (config : ReadyConfig State)
    (hConfig : config ∈ queryConfigs lts root initial)
    (action : Action) (Qpos : ProcSet Action Name) (observation : RSObs Action)
    (hChild : ∃ process', Deriv env (decode config.1) action process' ∧
      finiteCofinalRelation lts decode root initial process'
        (DerivSetOf env Qpos action) observation)
    (selected : StateSet State)
    (hSelected : selected ⊆ config.2)
    (hQpos : ∀ source, source ∈ selected → Qpos (decode source)) :
    ∃ successor, successor ∈ lts.next config.1 action ∧
      ∃ childCapability,
        ((successor, shift lts selected action), childCapability) ∈
          capabilityTable lts root initial ∧
        capLe childCapability (reqOfObs observation) := by
  rcases hChild with ⟨process', hDeriv, hCofinal⟩
  have hConfigUniverse := queryConfigs_subset_configUniverse lts env decode realizes
    root initial hRoot hInitial config hConfig
  rcases (mem_configUniverse_iff lts config.1 config.2).mp hConfigUniverse with
    ⟨hState, hCompetitors⟩
  rcases realizes.next_complete config.1 action process' hState hDeriv with
    ⟨successor, _, hNext, hDecode⟩
  have hSelectedListed : selected ⊆ (competitorsOf lts config.2).toFinset := by
    intro source hSource
    apply List.mem_toFinset.mpr
    exact (mem_competitorsOf_iff lts config.2 source).mpr
      ⟨by simpa using hCompetitors (hSelected hSource), hSelected hSource⟩
  have hQuery : (successor, shift lts selected action) ∈ queryConfigs lts root initial :=
    mem_queryConfigs_of_configSuccessor lts env decode realizes root initial
      hRoot hInitial config hConfig selected action successor
      (subset_mem_powerset (competitorsOf lts config.2) selected hSelectedListed)
      (realizes.action_complete action) hNext
  have hSubset : ∀ q, CCS.FiniteLTS.decodeSet decode
      (shift lts selected action) q → DerivSetOf env Qpos action q := by
    intro q hq
    rcases hq with ⟨target, hTarget, rfl⟩
    rcases (mem_shift_iff lts selected action target).mp hTarget with
      ⟨source, hSource, hSourceNext⟩
    exact ⟨decode source, hQpos source hSource,
      realizes.next_sound source action target hSourceNext⟩
  rcases hCofinal (successor, shift lts selected action) hQuery hDecode.symm hSubset with
    ⟨childCapability, hMember, hLe⟩
  exact ⟨successor, hNext, childCapability, hMember, hLe⟩

omit [DecidableEq Action] [DecidableEq State] in
/-- The capability join is the least common upper bound. -/
lemma capJoin_least {left right upper : Capability}
    (hLeft : capLe left upper) (hRight : capLe right upper) :
    capLe (capJoin left right) upper := by
  cases left <;> cases right <;> cases upper <;>
    simp [capLe, capJoin] at hLeft hRight ⊢

omit [DecidableEq Action] [DecidableEq State] in
/-- A compressed finite branch cover stays below the semantic node requirement. -/
lemma branchesRequirement_le_of_origins
    (negative neg : List Action)
    (branches : List (Branch Action State))
    (pos : List (Action × RSObs Action))
    (hNegEmpty : negative.isEmpty = neg.isEmpty)
    (hLength : branches.length ≤ pos.length)
    (hOrigins : ∀ branch, branch ∈ branches →
      ∃ i : Fin pos.length, capLe branch.capability (reqOfObs (pos.get i).2)) :
    capLe (branchesRequirement negative branches) (reqOfObs (.node pos neg)) := by
  have hChildren : capLe (branchCapabilities branches) (childrenReq pos) := by
    induction branches with
    | nil => simp [branchCapabilities, capLe]
    | cons branch branches ih =>
        simp only [branchCapabilities]
        apply capJoin_least
        · rcases hOrigins branch (by simp) with ⟨index, hBranch⟩
          exact capLe_trans hBranch (childrenReq_member_le (List.get_mem pos index))
        · apply ih (Nat.le_trans (Nat.le_succ _) (by simpa only [List.length_cons] using hLength))
          intro other hOther
          exact hOrigins other (by simp [hOther])
  have hShape : capLe
      (req (decide (1 < branches.length)) (!negative.isEmpty))
      (req (decide (1 < pos.length)) (!neg.isEmpty)) := by
    have hSim : decide (1 < branches.length) = true →
        decide (1 < pos.length) = true := by
      intro hBranch
      exact decide_eq_true_eq.mpr (Nat.lt_of_lt_of_le (decide_eq_true_eq.mp hBranch) hLength)
    rw [hNegEmpty]
    cases hBranch : decide (1 < branches.length) <;>
      cases hPos : decide (1 < pos.length) <;>
      cases hRefusal : !neg.isEmpty <;>
      simp [req, capLe, hBranch, hPos] at hSim ⊢
  simpa only [branchesRequirement, reqOfObs] using capJoin_mono hShape hChildren

/-- A finite partition satisfying the semantic node bounds produces a cofinal table entry. -/
lemma assignment_node_cofinal
    (lts : CCS.FiniteLTS Action State)
    (root : State) (initial : StateSet State)
    (config : ReadyConfig State)
    (hConfig : config ∈ queryConfigs lts root initial)
    (pos : List (Action × RSObs Action)) (neg negative : List Action)
    (assignment : Assignment Action)
    (hNegative : negative ∈ listPowerset lts.actions)
    (hRefuses : marks.refuses lts config.1 negative = true)
    (hAssignment : assignment ∈ assignments lts config.2)
    (hWellFormed : assignmentWellFormed assignment = true)
    (hValid : negativeAssignmentValid lts (competitorsOf lts config.2) negative
      assignment = true)
    (hChildren : ∀ branch, branch ∈
        assignmentBranches (competitorsOf lts config.2) assignment →
      ∃ successor, successor ∈ lts.next config.1 branch.action ∧
        ∃ childCapability,
          ((successor, shift lts branch.competitors branch.action), childCapability) ∈
            capabilityTable lts root initial ∧
          capLe childCapability branch.capability)
    (hNegEmpty : negative.isEmpty = neg.isEmpty)
    (hLength : (assignmentBranches (competitorsOf lts config.2) assignment).length ≤
      pos.length)
    (hOrigins : ∀ branch, branch ∈
        assignmentBranches (competitorsOf lts config.2) assignment →
      ∃ index : Fin pos.length,
        capLe branch.capability (reqOfObs (pos.get index).2)) :
    ∃ finiteCapability, (config, finiteCapability) ∈ capabilityTable lts root initial ∧
      capLe finiteCapability (reqOfObs (.node pos neg)) := by
  let branches := assignmentBranches (competitorsOf lts config.2) assignment
  let finiteCapability := branchesRequirement negative branches
  have hMark : marksSet lts
      ((capabilityTable lts root initial).toFinset : Set (CapabilityConfig State))
      config finiteCapability := by
    right
    refine ⟨negative, hNegative, hRefuses, assignment, hAssignment, hWellFormed,
      rfl, hValid, ?_⟩
    intro branch hBranch
    rcases hChildren branch hBranch with ⟨successor, hNext, childCapability,
      hChild, hLe⟩
    exact ⟨successor, hNext, childCapability, by simpa using hChild, hLe⟩
  have hCapability : finiteCapability ∈ capabilities := by
    cases finiteCapability <;> simp [capabilities]
  have hMember : (config, finiteCapability) ∈ capabilityTable lts root initial :=
    (capabilityConfigMem_iff _ _).mp
      (capabilityTable_closed lts root initial config finiteCapability hConfig hCapability
        ((marks_iff_marksSet lts _ config finiteCapability).mpr hMark))
  exact ⟨finiteCapability, hMember,
    branchesRequirement_le_of_origins negative neg branches pos hNegEmpty hLength hOrigins⟩

/-- Semantic cover chooses one positive index or the negative group for each finite competitor. -/
lemma semantic_node_choices
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (decode : State → CCS Action Name)
    (config : ReadyConfig State)
    (Q Qneg : ProcSet Action Name)
    (pos : List (Action × RSObs Action))
    (Qpos : Fin pos.length → ProcSet Action Name)
    (hSubset : ∀ process, CCS.FiniteLTS.decodeSet decode config.2 process → Q process)
    (hCover : ∀ process, Q process → Qneg process ∨ ∃ i, Qpos i process) :
    ∃ choice : State → Option (Fin pos.length),
      ∀ source, source ∈ competitorsOf lts config.2 →
        match choice source with
        | none => Qneg (decode source)
        | some index => Qpos index (decode source) := by
  classical
  let choice : State → Option (Fin pos.length) := fun source =>
    if h : ∃ index, Qpos index (decode source) then some (Classical.choose h) else none
  refine ⟨choice, ?_⟩
  intro source hListed
  have hSource := (mem_competitorsOf_iff lts config.2 source).mp hListed |>.2
  have hCovered := hCover (decode source) (hSubset (decode source) ⟨source, hSource, rfl⟩)
  by_cases hPositive : ∃ index, Qpos index (decode source)
  · simpa only [choice, dif_pos hPositive] using Classical.choose_spec hPositive
  · rcases hCovered with hNegative | hPositive'
    · simpa only [choice, dif_neg hPositive] using hNegative
    · exact (hPositive hPositive').elim

/-- Assign semantic positive indices to slots with their observation labels. -/
private def nodeChoiceAssignment (pos : List (Action × RSObs Action))
    (choice : State → Option (Fin pos.length)) (slots : List (Fin pos.length))
    (listed : List State) : Assignment Action :=
  listed.map (fun source => (choice source).map fun index =>
    (slots.idxOf index, (pos.get index).1, reqOfObs (pos.get index).2))

omit [DecidableEq State] in
private lemma nodeChoiceAssignment_wellFormed
    (pos : List (Action × RSObs Action))
    (choice : State → Option (Fin pos.length)) (slots : List (Fin pos.length))
    (listed : List State)
    (hSlots : ∀ source ∈ listed, ∀ index, choice source = some index → index ∈ slots) :
    assignmentWellFormed (nodeChoiceAssignment pos choice slots listed) = true := by
  induction listed with
  | nil => rfl
  | cons source listed ih =>
      cases hChoice : choice source with
      | none =>
          simpa [nodeChoiceAssignment, hChoice] using ih (fun other hOther index hIndex =>
            hSlots other (by simp [hOther]) index hIndex)
      | some index =>
          simp only [nodeChoiceAssignment, List.map_cons, hChoice, Option.map_some,
            assignmentWellFormed, Bool.and_eq_true]
          refine ⟨List.all_eq_true.mpr ?_, ih (fun other hOther otherIndex hIndex =>
            hSlots other (by simp [hOther]) otherIndex hIndex)⟩
          intro entry hEntry
          rcases List.mem_map.mp hEntry with ⟨other, _, rfl⟩
          cases hOther : choice other with
          | none => simp
          | some otherIndex =>
              by_cases hIndex : slots.idxOf index = slots.idxOf otherIndex
              · have hEqual : index = otherIndex :=
                  (List.idxOf_inj (hSlots source (by simp) index hChoice)).mp hIndex
                simp [hEqual]
              · simp [hIndex]

omit [DecidableEq Action] in
private lemma branchInsert_slots (slot : Nat) (action : Action)
    (capability : Capability) (competitor : State)
    (branches : List (Branch Action State)) :
    (branchInsert slot action capability competitor branches).map Branch.slot =
      if slot ∈ branches.map Branch.slot then branches.map Branch.slot
      else (branches.map Branch.slot).concat slot := by
  induction branches with
  | nil => simp [branchInsert]
  | cons branch branches ih =>
      by_cases hSlot : slot = branch.slot
      · simp [branchInsert, hSlot]
      · simp [branchInsert, hSlot, ih, List.concat_eq_append]
        split_ifs <;> rfl

omit [DecidableEq Action] in
private lemma assignmentBranches_slots_nodup (listed : List State)
    (assignment : Assignment Action) :
    (assignmentBranches listed assignment |>.map Branch.slot).Nodup := by
  induction listed generalizing assignment with
  | nil => cases assignment <;> simp [assignmentBranches]
  | cons source listed ih =>
      cases assignment with
      | nil => simp [assignmentBranches]
      | cons choice assignment =>
          cases choice with
          | none => exact ih assignment
          | some entry =>
              rcases entry with ⟨slot, action, capability⟩
              change (branchInsert slot action capability source
                (assignmentBranches listed assignment) |>.map Branch.slot).Nodup
              rw [branchInsert_slots]
              split_ifs with hSlot
              · exact ih assignment
              · exact (List.nodup_concat _ _).mpr ⟨hSlot, ih assignment⟩

omit [DecidableEq Action] [DecidableEq State] in
private lemma nodeChoiceAssignment_entry (pos : List (Action × RSObs Action))
  (choice : State → Option (Fin pos.length)) (slots : List (Fin pos.length))
  (listed : List State)
    (slot : Nat) (action : Action) (capability : Capability)
  (hEntry : some (slot, action, capability) ∈ nodeChoiceAssignment pos choice slots listed) :
  ∃ index : Fin pos.length, slots.idxOf index = slot ∧
      (pos.get index).1 = action ∧ reqOfObs (pos.get index).2 = capability := by
  rcases List.mem_map.mp hEntry with ⟨source, _, hEntry⟩
  cases hChoice : choice source with
  | none => simp [hChoice] at hEntry
  | some index =>
      simp only [hChoice, Option.map_some, Option.some.injEq] at hEntry
      cases hEntry
      exact ⟨index, rfl, rfl, rfl⟩

omit [DecidableEq Action] in
private lemma nodeChoiceAssignment_branches_length (pos : List (Action × RSObs Action))
    (choice : State → Option (Fin pos.length)) (slots : List (Fin pos.length))
    (listed : List State) :
    (assignmentBranches listed (nodeChoiceAssignment pos choice slots listed)).length ≤
      pos.length := by
  classical
  let assignment := nodeChoiceAssignment pos choice slots listed
  let branches := assignmentBranches listed assignment
  have hSlots := assignmentBranches_slots_nodup listed assignment
  change (branches.map Branch.slot).Nodup at hSlots
  have hOrigin (index : Fin branches.length) :
      ∃ semantic : Fin pos.length, slots.idxOf semantic = (branches.get index).slot := by
    rcases nodeChoiceAssignment_entry pos choice slots listed _ _ _
      (assignmentBranches_label_origin listed assignment (branches.get index)
        (List.get_mem branches index)) with ⟨semantic, hSlot, _, _⟩
    exact ⟨semantic, hSlot⟩
  let origin : Fin branches.length → Fin pos.length := fun index => Classical.choose (hOrigin index)
  have hOriginSlot (index : Fin branches.length) :
      slots.idxOf (origin index) = (branches.get index).slot :=
    Classical.choose_spec (hOrigin index)
  have hInjective : Function.Injective origin := by
    intro left right hEqual
    have hSlotEqual : (branches.get left).slot = (branches.get right).slot := by
      calc
        _ = slots.idxOf (origin left) := (hOriginSlot left).symm
        _ = slots.idxOf (origin right) := congrArg (slots.idxOf ·) hEqual
        _ = _ := hOriginSlot right
    apply Fin.ext
    change branches[left.val].slot = branches[right.val].slot at hSlotEqual
    have hMapped : (branches.map Branch.slot)[left.val] =
        (branches.map Branch.slot)[right.val] := by
      simpa only [List.getElem_map] using hSlotEqual
    exact (List.Nodup.getElem_inj_iff hSlots).mp hMapped
  simpa using Fintype.card_le_of_injective origin hInjective

omit [DecidableEq Action] in
private lemma branchInsert_member_slot (slot : Nat) (action : Action)
    (capability : Capability) (competitor : State)
    (branches : List (Branch Action State)) (branch : Branch Action State)
    (member : State) (hBranch : branch ∈ branchInsert slot action capability competitor branches)
    (hMember : member ∈ branch.competitors) :
    (member = competitor ∧ branch.slot = slot) ∨
      ∃ prior ∈ branches, member ∈ prior.competitors ∧ branch.slot = prior.slot := by
  induction branches generalizing branch with
  | nil =>
      simp [branchInsert] at hBranch
      subst branch
      exact Or.inl ⟨by simpa using hMember, rfl⟩
  | cons current remaining ih =>
      unfold branchInsert at hBranch
      split at hBranch
      · rename_i hSlot
        rcases List.mem_cons.mp hBranch with rfl | hTail
        · rcases Finset.mem_insert.mp hMember with hNew | hPrior
          · exact Or.inl ⟨hNew, (beq_iff_eq.mp hSlot).symm⟩
          · exact Or.inr ⟨current, by simp, hPrior, rfl⟩
        · exact Or.inr ⟨branch, by simp [hTail], hMember, rfl⟩
      · rcases List.mem_cons.mp hBranch with rfl | hTail
        · exact Or.inr ⟨branch, by simp, hMember, rfl⟩
        · rcases ih branch hTail hMember with hNew | ⟨prior, hPrior, hPriorMember, hSlot⟩
          · exact Or.inl hNew
          · exact Or.inr ⟨prior, by simp [hPrior], hPriorMember, hSlot⟩

omit [DecidableEq Action] in
private lemma nodeChoiceAssignment_branch_member (pos : List (Action × RSObs Action))
    (choice : State → Option (Fin pos.length)) (slots : List (Fin pos.length))
    (listed : List State) (branch : Branch Action State) (member : State)
    (hBranch : branch ∈ assignmentBranches listed (nodeChoiceAssignment pos choice slots listed))
    (hMember : member ∈ branch.competitors) :
    ∃ index : Fin pos.length, choice member = some index ∧ slots.idxOf index = branch.slot := by
  induction listed generalizing branch with
  | nil => simp [nodeChoiceAssignment, assignmentBranches] at hBranch
  | cons source listed ih =>
      cases hChoice : choice source with
      | none =>
          exact ih branch (by simpa [nodeChoiceAssignment, hChoice, assignmentBranches]
            using hBranch) hMember
      | some index =>
          rcases branchInsert_member_slot (slots.idxOf index) (pos.get index).1
            (reqOfObs (pos.get index).2) source
            (assignmentBranches listed (nodeChoiceAssignment pos choice slots listed))
            branch member (by simpa [nodeChoiceAssignment, hChoice, assignmentBranches]
              using hBranch) hMember with
            ⟨rfl, hSlot⟩ | ⟨prior, hPrior, hPriorMember, hSlot⟩
          · exact ⟨index, hChoice, hSlot.symm⟩
          · rcases ih prior hPrior hPriorMember with ⟨priorIndex, hPriorChoice, hPriorSlot⟩
            exact ⟨priorIndex, hPriorChoice, hPriorSlot.trans hSlot.symm⟩

private lemma nodeChoiceAssignment_enumerated
    (lts : CCS.FiniteLTS Action State)
    (competitors : StateSet State)
    (pos : List (Action × RSObs Action))
    (choice : State → Option (Fin pos.length))
    (slots : List (Fin pos.length))
    (hSlots : ∀ source ∈ competitorsOf lts competitors,
      ∀ index, choice source = some index → index ∈ slots)
    (hLength : slots.length ≤ (competitorsOf lts competitors).length)
    (hActions : ∀ index : Fin pos.length, (pos.get index).1 ∈ lts.actions) :
    nodeChoiceAssignment pos choice slots (competitorsOf lts competitors) ∈
      assignments lts competitors := by
  apply (mem_assignments_iff lts competitors _).mpr
  refine ⟨by simp [nodeChoiceAssignment], ?_⟩
  intro entry hEntry
  rcases List.mem_map.mp hEntry with ⟨source, hSource, rfl⟩
  cases hChoice : choice source with
  | none => simp [assignmentChoices]
  | some index =>
      apply (mem_assignmentChoices_iff lts _ _).mpr
      right
      refine ⟨slots.idxOf index, List.mem_range.mpr ?_,
        (pos.get index).1, hActions index,
        reqOfObs (pos.get index).2, ?_, rfl⟩
      · exact lt_of_lt_of_le (List.idxOf_lt_length_of_mem (hSlots source hSource index hChoice))
          hLength
      · cases reqOfObs (pos.get index).2 <;> simp [capabilities]

/-- Finite and semantic raw Ready capabilities are sound and downward-cofinal. -/
private theorem readyCapabilities_correct_skeleton
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (capability : Capability)
    (hState : state ∈ lts.states)
    (hCompetitors : competitors ⊆ lts.states.toFinset) :
    capability ∈ readyCapabilities lts state competitors ↔
      lfpDRSAbsExactCanon env (decode state)
        (CCS.FiniteLTS.decodeSet decode competitors) capability := by
  let finiteRaw : Capability → Prop :=
    fun candidate => ((state, competitors), candidate) ∈ capabilityTable lts state competitors
  let semanticRaw : Capability → Prop :=
    alphaCapRaw rsObsCap
      (lfpDRS env (decode state) (CCS.FiniteLTS.decodeSet decode competitors))
  have raw_sound : ∀ candidate, finiteRaw candidate → semanticRaw candidate := by
    intro candidate hCandidate
    exact capabilityTable_raw_sound lts env decode realizes state competitors
      hState hCompetitors ((state, competitors), candidate) hCandidate
  have node_step : ∀ (process : CCS Action Name) (Q : ProcSet Action Name)
      (pos : List (Action × RSObs Action)) (neg : List Action),
      DRS env (finiteCofinalRelation lts decode state competitors) process Q (.node pos neg) →
      finiteCofinalRelation lts decode state competitors process Q (.node pos neg) := by
    intro process Q pos neg hStep config hConfig hProcess hSubset
    cases pos with
    | nil =>
        rcases config with ⟨source, selected⟩
        have hSource : source ∈ lts.states :=
          ((mem_configUniverse_iff lts source selected).mp
            (queryConfigs_subset_configUniverse lts env decode realizes state competitors
              hState hCompetitors (source, selected) hConfig)).1
        subst process
        exact refusal_only_step_cofinal lts env decode realizes state competitors source selected
          neg hSource hConfig Q hSubset hStep
    | cons head tail =>
        rcases hStep with ⟨Qneg, Qpos, hPos, hRefuse, hEnabled, hCover⟩
        subst process
        let listed := competitorsOf lts config.2
        rcases semantic_node_choices lts decode config Q Qneg (head :: tail) Qpos
          hSubset hCover with ⟨choice, hChoice⟩
        let slots := listed.filterMap choice
        let assignment := nodeChoiceAssignment (head :: tail) choice slots listed
        have hSlots : ∀ source ∈ listed, ∀ index, choice source = some index →
            index ∈ slots := by
          intro source hSource index hIndex
          exact List.mem_filterMap.mpr ⟨source, hSource, hIndex⟩
        have hSlotLength : slots.length ≤ listed.length := by
          exact List.length_filterMap_le choice listed
        have hAssignment : assignment ∈ assignments lts config.2 := by
          apply nodeChoiceAssignment_enumerated lts config.2 (head :: tail) choice slots
          · exact hSlots
          · exact hSlotLength
          · intro index
            exact realizes.action_complete _
        have hWellFormed : assignmentWellFormed assignment = true :=
          nodeChoiceAssignment_wellFormed (head :: tail) choice slots listed hSlots
        have hListed : config.1 ∈ lts.states :=
          ((mem_configUniverse_iff lts config.1 config.2).mp
            (queryConfigs_subset_configUniverse lts env decode realizes state competitors
              hState hCompetitors config hConfig)).1
        let negative := lts.actions.filter (fun action => decide (action ∈ neg))
        have hNegative : negative ∈ listPowerset lts.actions :=
          filter_mem_listPowerset lts.actions _
        have hRefuses : marks.refuses lts config.1 negative = true :=
          (refuses_iff lts env decode realizes config.1 negative hListed).mpr (by
            intro action hAction
            exact hRefuse action (decide_eq_true_eq.mp (List.mem_filter.mp hAction).2))
        have hNegEmpty : negative.isEmpty = neg.isEmpty := by
          cases neg with
          | nil => simp [negative]
          | cons action rest =>
              have hAction : action ∈ negative := by
                simp [negative, realizes.action_complete action]
              have hNonempty : negative.isEmpty = false := by
                cases hList : negative with
                | nil => simp [hList] at hAction
                | cons _ _ => simp
              simpa using hNonempty
        have hValid : negativeAssignmentValid lts listed negative assignment = true := by
          apply (negativeAssignmentValid_iff lts listed negative assignment).mpr
          change List.Forall₂ (NegativeAssignmentCondition lts negative) listed
            (listed.map (fun source => (choice source).map fun index =>
              (slots.idxOf index, ((head :: tail).get index).1,
                reqOfObs ((head :: tail).get index).2)))
          have hForall : ∀ sources : List State,
              (∀ source, source ∈ sources → source ∈ listed) →
              List.Forall₂ (NegativeAssignmentCondition lts negative) sources
                (sources.map (fun source => (choice source).map fun index =>
                  (slots.idxOf index, ((head :: tail).get index).1,
                    reqOfObs ((head :: tail).get index).2))) := by
            intro sources hSources
            induction sources with
            | nil => exact List.Forall₂.nil
            | cons source sources ih =>
                apply List.Forall₂.cons ?_ (ih (fun member hMember =>
                  hSources member (by simp [hMember])))
                intro hNone
                cases hChoiceSource : choice source with
                | some index => simp [hChoiceSource] at hNone
                | none =>
                    have hNegativeSource : Qneg (decode source) := by
                      simpa [hChoiceSource] using hChoice source
                        (hSources source (by simp))
                    rcases hEnabled (decode source) hNegativeSource with
                      ⟨action, hAction, hEnabledAction⟩
                    have hSourceListed : source ∈ lts.states :=
                      ((mem_competitorsOf_iff lts config.2 source).mp
                        (hSources source (by simp))).1
                    refine ⟨action, List.mem_filter.mpr ⟨realizes.action_complete action,
                      decide_eq_true_eq.mpr hAction⟩, ?_⟩
                    cases hEmpty : (lts.next source action).isEmpty with
                    | false => rfl
                    | true =>
                        have hDisabled := (next_isEmpty_iff_not_enabled lts env decode realizes
                          source action hSourceListed).mp hEmpty
                        exact (hDisabled hEnabledAction).elim
          exact hForall listed (fun _ hMember => hMember)
        have hLength : (assignmentBranches listed assignment).length ≤
            (head :: tail).length :=
          nodeChoiceAssignment_branches_length (head :: tail) choice slots listed
        have hOrigins : ∀ branch ∈ assignmentBranches listed assignment,
            ∃ index : Fin (head :: tail).length,
              capLe branch.capability (reqOfObs ((head :: tail).get index).2) := by
          intro branch hBranch
          have hEntry := assignmentBranches_label_origin listed assignment branch hBranch
          rcases nodeChoiceAssignment_entry (head :: tail) choice slots listed
            branch.slot branch.action branch.capability hEntry with
            ⟨index, _, _, hCapability⟩
          refine ⟨index, ?_⟩
          rw [← hCapability]
          exact capLe_refl _
        have hChildren : ∀ branch ∈ assignmentBranches listed assignment,
            ∃ successor, successor ∈ lts.next config.1 branch.action ∧
              ∃ childCapability,
                ((successor, shift lts branch.competitors branch.action), childCapability) ∈
                  capabilityTable lts state competitors ∧
                capLe childCapability branch.capability := by
          intro branch hBranch
          have hEntry := assignmentBranches_label_origin listed assignment branch hBranch
          rcases nodeChoiceAssignment_entry (head :: tail) choice slots listed
            branch.slot branch.action branch.capability hEntry with
            ⟨index, hIndexSlot, hAction, hCapability⟩
          have hSelected : branch.competitors ⊆ config.2 := by
            intro source hSource
            have hListedSource := assignmentBranches_competitors_subset listed assignment
              branch source hBranch hSource
            exact ((mem_competitorsOf_iff lts config.2 source).mp hListedSource).2
          have hQpos : ∀ source, source ∈ branch.competitors →
              Qpos index (decode source) := by
            intro source hSource
            have hListedSource := assignmentBranches_competitors_subset listed assignment
              branch source hBranch hSource
            rcases nodeChoiceAssignment_branch_member (head :: tail) choice slots listed
              branch source hBranch hSource with ⟨otherIndex, hOtherChoice, hOtherSlot⟩
            have hSame : otherIndex = index :=
              (List.idxOf_inj (hSlots source hListedSource otherIndex hOtherChoice)).mp
                (hOtherSlot.trans hIndexSlot.symm)
            subst otherIndex
            simpa [hOtherChoice] using hChoice source hListedSource
          rcases finiteCofinalRelation_child lts env decode realizes state competitors
            hState hCompetitors config hConfig ((head :: tail).get index).1
            (Qpos index) ((head :: tail).get index).2 (hPos index)
            branch.competitors hSelected hQpos with
            ⟨successor, hNext, childCapability, hChild, hChildLe⟩
          exact ⟨successor, by simpa only [hAction] using hNext,
            childCapability, by simpa only [hAction] using hChild,
            by simpa only [hCapability] using hChildLe⟩
        exact assignment_node_cofinal lts state competitors config hConfig
          (head :: tail) neg negative assignment hNegative hRefuses hAssignment
          hWellFormed hValid hChildren hNegEmpty hLength hOrigins
  have raw_cofinal : ∀ candidate, semanticRaw candidate →
      ∃ finiteCandidate, finiteRaw finiteCandidate ∧ capLe finiteCandidate candidate := by
    intro candidate hCandidate
    rcases hCandidate with ⟨observation, hObservation, hRequirement⟩
    have hCofinal : finiteCofinalRelation lts decode state competitors (decode state)
        (CCS.FiniteLTS.decodeSet decode competitors) observation := by
      apply hObservation (finiteCofinalRelation lts decode state competitors)
      intro process Q observation hStep
      cases observation with
      | tt => exact finiteCofinalRelation_tt lts env decode state competitors process Q hStep
      | node pos neg => exact node_step process Q pos neg hStep
    rcases hCofinal (state, competitors) (mem_queryConfigs lts state competitors) rfl
      (fun _ hMember => hMember) with ⟨finiteCandidate, hFinite, hFiniteLe⟩
    exact ⟨finiteCandidate, hFinite, capLe_trans hFiniteLe hRequirement⟩
  have minimal_agree : minimalCap finiteRaw capability ↔ minimalCap semanticRaw capability :=
    minimalCap_iff_of_sound_and_cofinal finiteRaw semanticRaw raw_sound raw_cofinal capability
  have finite_minimal :
      capability ∈ readyCapabilities lts state competitors ↔ minimalCap finiteRaw capability := by
    simpa [readyCapabilities, finiteRaw] using
      (mem_minimalCapabilities_iff (capabilityTable lts state competitors) (state, competitors) capability)
  have semantic_minimal :
      minimalCap semanticRaw capability ↔
        lfpDRSAbsExactCanon env (decode state)
          (CCS.FiniteLTS.decodeSet decode competitors) capability := by
    rfl
  exact finite_minimal.trans (minimal_agree.trans semantic_minimal)

/-- A realized finite Ready evaluator computes the exact concrete lfp capability antichain. -/
theorem readyCapabilities_correct
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
    (state : State)
    (competitors : StateSet State)
    (capability : Capability)
    (hState : state ∈ lts.states)
    (hCompetitors : ∀ competitor, competitor ∈ competitors → competitor ∈ lts.states) :
    capability ∈ readyCapabilities lts state competitors ↔
      lfpDRSAbsExactCanon env (decode state)
        (CCS.FiniteLTS.decodeSet decode competitors) capability := by
  apply readyCapabilities_correct_skeleton lts env decode realizes state competitors capability
    hState
  intro competitor hCompetitor
  simpa using hCompetitors competitor hCompetitor

/-- A realized finite threshold query is equivalent to semantic Ready failure. -/
theorem failsAt_correct
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (realizes : CCS.FiniteLTS.Realizes lts env decode)
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
      (readyCapabilities_correct lts env decode realizes state competitors capability
        hState hCompetitors).mp hMember,
      (capLeBool_iff capability threshold).mp hLe⟩
  · rintro ⟨capability, hCapability, hLe⟩
    apply List.any_eq_true.mpr
    exact ⟨capability,
      (readyCapabilities_correct lts env decode realizes state competitors capability
        hState hCompetitors).mpr hCapability,
      (capLeBool_iff capability threshold).mpr hLe⟩

end FiniteLTS
end EqCheckingAbstractInterpretation.Ready
