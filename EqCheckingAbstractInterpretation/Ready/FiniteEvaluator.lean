import EqCheckingAbstractInterpretation.CCS.FiniteLTS
import EqCheckingAbstractInterpretation.FiniteEvaluator.Basic
import EqCheckingAbstractInterpretation.Ready.Basic

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.FiniteEvaluator

universe u v

namespace FiniteLTS

variable {Action : Type u} {State : Type v}
  [DecidableEq Action] [DecidableEq State]

abbrev StateSet (State : Type v) := FSet State
abbrev ReadyConfig (State : Type v) := State × StateSet State
abbrev CapabilityConfig (State : Type v) := ReadyConfig State × Capability
abbrev CapabilityTable (State : Type v) := List (CapabilityConfig State)

/-- Shift a finite competitor set through one action. -/
def shift (lts : CCS.FiniteLTS Action State) (competitors : StateSet State)
    (action : Action) : StateSet State :=
  competitors.biUnion (fun state => (lts.next state action).toFinset)

def configMem (config : ReadyConfig State) : List (ReadyConfig State) → Bool
  | [] => false
  | (state, competitors) :: configs =>
    decide (config.1 = state ∧ config.2 = competitors) || configMem config configs

def configInsert (config : ReadyConfig State) (configs : List (ReadyConfig State)) :
    List (ReadyConfig State) :=
  if configMem config configs then configs else config :: configs

def configUnion (left right : List (ReadyConfig State)) : List (ReadyConfig State) :=
  left.foldl (fun configs config => configInsert config configs) right

/-- Boolean capability order, aligned with `capLe`. -/
def capLeBool : Capability → Capability → Bool
  | .T, _ => true
  | .S, .S => true
  | .S, .RS => true
  | .F, .F => true
  | .F, .RS => true
  | .RS, .RS => true
  | _, _ => false

def capabilities : List Capability := [.T, .S, .F, .RS]

def capabilityConfigMem (config : CapabilityConfig State) : CapabilityTable State → Bool
  | [] => false
  | ((state, competitors), capability) :: configs =>
    decide (config.1.1 = state ∧ config.1.2 = competitors ∧ config.2 = capability) ||
      capabilityConfigMem config configs

/-- A capability holds at a configuration when some derived requirement is below it. -/
def markedAt (marked : CapabilityTable State) (config : ReadyConfig State)
    (threshold : Capability) : Bool :=
  marked.any (fun entry =>
    decide (entry.1.1 = config.1 ∧ entry.1.2 = config.2) && capLeBool entry.2 threshold)

/-- All ways to assign each competitor either to the negative set or a positive branch. -/
abbrev Assignment (Action : Type u) := List (Option (Nat × Action × Capability))

structure Branch (Action : Type u) (State : Type v) where
  slot : Nat
  action : Action
  capability : Capability
  competitors : StateSet State

def assignmentChoices (lts : CCS.FiniteLTS Action State) (slots : List Nat) :
    List (Option (Nat × Action × Capability)) :=
  none :: slots.flatMap (fun slot => lts.actions.flatMap (fun action =>
    capabilities.map (fun capability => some (slot, action, capability))))

def assignmentsWithSlots (lts : CCS.FiniteLTS Action State) (slots : List Nat) : List State →
    List (Assignment Action)
  | [] => [[]]
  | _ :: competitors =>
    (assignmentsWithSlots lts slots competitors).flatMap
      (fun tail => (assignmentChoices lts slots).map (fun choice => choice :: tail))

def competitorsOf (lts : CCS.FiniteLTS Action State) (competitors : StateSet State) : List State :=
  lts.states.filter (fun state => decide (state ∈ competitors))

def assignments (lts : CCS.FiniteLTS Action State) (competitors : StateSet State) :
    List (Assignment Action) :=
  assignmentsWithSlots lts (List.range (competitorsOf lts competitors).length)
    (competitorsOf lts competitors)

def assignmentWellFormed : Assignment Action → Bool
  | [] => true
  | none :: assignments => assignmentWellFormed assignments
  | some (slot, action, capability) :: assignments =>
    assignments.all (fun choice => match choice with
      | none => true
      | some (otherSlot, otherAction, otherCapability) =>
        slot != otherSlot ||
          (decide (action = otherAction) && decide (capability = otherCapability))) &&
      assignmentWellFormed assignments

def branchInsert (slot : Nat) (action : Action) (capability : Capability) (competitor : State) :
    List (Branch Action State) → List (Branch Action State)
  | [] => [{ slot, action, capability, competitors := {competitor} }]
  | branch :: branches =>
    if slot == branch.slot then
      { branch with competitors := insert competitor branch.competitors } :: branches
    else
      branch :: branchInsert slot action capability competitor branches

def assignmentBranches : List State → Assignment Action → List (Branch Action State)
  | [], [] => []
  | _ :: competitors, none :: assignments =>
    assignmentBranches competitors assignments
  | competitor :: competitors, some (slot, action, capability) :: assignments =>
    branchInsert slot action capability competitor (assignmentBranches competitors assignments)
  | _, _ => []

def branchCapabilities : List (Branch Action State) → Capability
  | [] => .T
  | branch :: branches => capJoin branch.capability (branchCapabilities branches)

def branchesRequirement (negative : List Action) (branches : List (Branch Action State)) : Capability :=
  capJoin (req (decide (1 < branches.length)) (!negative.isEmpty))
    (branchCapabilities branches)

/-- Verify the negative-group obligation of a finite Ready partition. -/
def negativeAssignmentValid (lts : CCS.FiniteLTS Action State) (competitors : List State)
    (negative : List Action) : Assignment Action → Bool
  | [] => competitors.isEmpty
  | none :: assignments =>
    match competitors with
    | [] => false
    | competitor :: competitors =>
      (negative.any (fun action => !(lts.next competitor action).isEmpty)) &&
        negativeAssignmentValid lts competitors negative assignments
  | some _ :: assignments =>
    match competitors with
    | [] => false
    | _ :: competitors => negativeAssignmentValid lts competitors negative assignments

/-- Verify all positive-branch obligations of a finite Ready partition. -/
def branchesValid (lts : CCS.FiniteLTS Action State) (marked : CapabilityTable State)
    (state : State) : List (Branch Action State) → Bool
  | [] => true
  | branch :: branches =>
    (lts.next state branch.action).any (fun successor =>
      markedAt marked (successor, shift lts branch.competitors branch.action) branch.capability) &&
      branchesValid lts marked state branches

/-- Does one symbolic Ready step derive precisely the requested capability? -/
def marks (lts : CCS.FiniteLTS Action State) (marked : CapabilityTable State)
    (config : ReadyConfig State) (capability : Capability) : Bool :=
  (decide (config.2 = ∅) && decide (capability = .T)) ||
    (listPowerset lts.actions).any (fun negative =>
      refuses lts config.1 negative &&
        (assignments lts config.2).any (fun assignment =>
          assignmentWellFormed assignment &&
            let branches := assignmentBranches (competitorsOf lts config.2) assignment
            decide (branchesRequirement negative branches = capability) &&
              negativeAssignmentValid lts (competitorsOf lts config.2) negative assignment &&
                branchesValid lts marked config.1 branches))
where
  refuses (lts : CCS.FiniteLTS Action State) (state : State) (negative : List Action) : Bool :=
    negative.all (fun action => (lts.next state action).isEmpty)

/-- Direct successors needed by all finite partitions at a Ready configuration. -/
def configSuccessors (lts : CCS.FiniteLTS Action State) (config : ReadyConfig State) :
    List (ReadyConfig State) :=
  (powerset (competitorsOf lts config.2)).flatMap (fun competitors =>
    lts.actions.flatMap (fun action =>
      (lts.next config.1 action).map (fun successor => (successor, shift lts competitors action))))

/-- All state-and-competitor configurations expressible by the finite LTS. -/
def configUniverse (lts : CCS.FiniteLTS Action State) : List (ReadyConfig State) :=
  lts.states.flatMap (fun state =>
    (powerset lts.states).map (fun competitors => (state, competitors)))

def expandConfigs (lts : CCS.FiniteLTS Action State) (configs : List (ReadyConfig State)) :
    List (ReadyConfig State) :=
  configs.foldl (fun closure config => configUnion (configSuccessors lts config) closure) configs

/-- Derivative-closed finite domain needed to evaluate one process-versus-set query. -/
def queryConfigs (lts : CCS.FiniteLTS Action State) (state : State)
    (competitors : StateSet State) : List (ReadyConfig State) :=
  let bound := lts.states.length * 2 ^ lts.states.length
  (List.replicate bound ()).foldl (fun configs _ => expandConfigs lts configs) [(state, competitors)]

def capabilityConfigs (configs : List (ReadyConfig State)) : List (CapabilityConfig State) :=
  configs.flatMap (fun config => capabilities.map (fun capability => (config, capability)))

/- Saturate the symbolic Ready transformer over the query's finite domain. -/
def capabilityTable (lts : CCS.FiniteLTS Action State) (state : State)
    (competitors : StateSet State) : CapabilityTable State :=
  let configs := queryConfigs lts state competitors
  saturate (capabilityConfigs configs) capabilityConfigMem
    (fun marked config => marks lts marked config.1 config.2)

def minimalCapabilities (marked : CapabilityTable State) (config : ReadyConfig State) : List Capability :=
  capabilities.filter (fun capability =>
    capabilityConfigMem (config, capability) marked &&
      !capabilities.any (fun smaller =>
        !(decide (smaller = capability)) && capabilityConfigMem (config, smaller) marked &&
          capLeBool smaller capability))

/--
Finite exact-capability query for the symbolic Ready transformer.  The result
is the minimal antichain of capability requirements derived at the query.
-/
def readyCapabilities (lts : CCS.FiniteLTS Action State) (state : State)
    (competitors : StateSet State) : List Capability :=
  minimalCapabilities (capabilityTable lts state competitors) (state, competitors)

/-- Does the finite capability result refute the given threshold preorder? -/
def failsAt (lts : CCS.FiniteLTS Action State) (threshold : Capability)
    (state : State) (competitors : StateSet State) : Bool :=
  (readyCapabilities lts state competitors).any (fun capability => capLeBool capability threshold)

end FiniteLTS
end EqCheckingAbstractInterpretation.Ready
