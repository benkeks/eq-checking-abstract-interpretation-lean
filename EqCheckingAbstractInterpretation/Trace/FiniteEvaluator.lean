import EqCheckingAbstractInterpretation.CCS.FiniteLTS
import EqCheckingAbstractInterpretation.FiniteEvaluator.Basic

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.FiniteEvaluator

universe u v

namespace FiniteLTS

variable {Action : Type u} {State : Type v}
  [DecidableEq Action] [DecidableEq State]

abbrev StateSet (State : Type v) := FSet State
abbrev Config (State : Type v) := State × StateSet State
abbrev MarkerTable (State : Type v) := List (Config State)

/-- Shift a finite competitor set through one action. -/
def shift (lts : CCS.FiniteLTS Action State) (competitors : StateSet State)
    (action : Action) : StateSet State :=
  competitors.biUnion (fun state => (lts.next state action).toFinset)

def configMem (config : Config State) : MarkerTable State → Bool
  | [] => false
  | (state, competitors) :: configs =>
    decide (config.1 = state ∧ config.2 = competitors) || configMem config configs

def configs (lts : CCS.FiniteLTS Action State) : List (Config State) :=
  lts.states.flatMap (fun state => (powerset lts.states).map (fun competitors => (state, competitors)))

/-- Boolean form of the two `DTrSharp` clauses at one configuration. -/
def marks (lts : CCS.FiniteLTS Action State) (marked : MarkerTable State)
    (state : State) (competitors : StateSet State) : Bool :=
  decide (competitors = ∅) ||
    lts.actions.any (fun action =>
      (lts.next state action).any (fun successor =>
        configMem (successor, shift lts competitors action) marked))

def successors (lts : CCS.FiniteLTS Action State) : Config State → MarkerTable State
  | (state, competitors) =>
    lts.actions.flatMap (fun action =>
      (lts.next state action).map (fun successor =>
        (successor, shift lts competitors action)))

def reachUntil (lts : CCS.FiniteLTS Action State) :
    Nat → MarkerTable State → MarkerTable State
  | 0, seen => seen
  | fuel + 1, seen =>
    let fresh := (seen.flatMap (successors lts)).filter (fun config => !configMem config seen)
    if fresh.isEmpty then seen else reachUntil lts fuel (seen ++ fresh.eraseDups)

def reachableConfigs (lts : CCS.FiniteLTS Action State)
    (initial : Config State) : MarkerTable State :=
  reachUntil lts (lts.states.length * 2 ^ lts.states.length + 1) [initial]

/-- Saturated Boolean form of `DTrSharp` over a finite transition system. -/
def markerTable (lts : CCS.FiniteLTS Action State) : MarkerTable State :=
  saturate (configs lts) configMem (fun marked config => marks lts marked config.1 config.2)

/-- Executable finite-state approximation of `AbstractDiff`. -/
def abstractDiff (lts : CCS.FiniteLTS Action State) (state : State)
    (competitors : StateSet State) : Bool :=
  configMem (state, competitors) (markerTable lts)

/-- Evaluate one abstract-difference query on its reachable configurations. -/
def abstractDiffReachable (lts : CCS.FiniteLTS Action State) (state : State)
    (competitors : StateSet State) : Bool :=
  let relevant := reachableConfigs lts (state, competitors)
  configMem (state, competitors)
    (saturate relevant configMem (fun marked config => marks lts marked config.1 config.2))

def tracePreordered (lts : CCS.FiniteLTS Action State) (left_state : State)
    (right_state : State) : Bool :=
  ¬ abstractDiffReachable lts left_state {right_state}

end FiniteLTS
end EqCheckingAbstractInterpretation.Trace
