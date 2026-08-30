import EqCheckingAbstractInterpretation.CCS.FiniteLTS
import EqCheckingAbstractInterpretation.FiniteEvaluator.Basic

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.FiniteEvaluator

universe u v

namespace FiniteLTS

variable {Action : Type u} {State : Type v} [BEq Action] [BEq State]

abbrev StateSet (State : Type v) := Set State
abbrev Config (State : Type v) := State × StateSet State
abbrev MarkerTable (State : Type v) := List (Config State)

/-- Shift a finite competitor set through one action. -/
def shift (lts : CCS.FiniteLTS Action State) (competitors : StateSet State)
    (action : Action) : StateSet State :=
  competitors.foldl (fun successors state => union successors (lts.next state action)) []

def configMem (config : Config State) : MarkerTable State → Bool
  | [] => false
  | (state, competitors) :: configs =>
    (config.1 == state && setEq config.2 competitors) || configMem config configs

def configs (lts : CCS.FiniteLTS Action State) : List (Config State) :=
  lts.states.flatMap (fun state => powerset lts.states |>.map (fun competitors => (state, competitors)))

/-- Boolean form of the two `DTrSharp` clauses at one configuration. -/
def marks (lts : CCS.FiniteLTS Action State) (marked : MarkerTable State)
    (state : State) (competitors : StateSet State) : Bool :=
  competitors.isEmpty ||
    lts.actions.any (fun action =>
      (lts.next state action).any (fun successor =>
        configMem (successor, shift lts competitors action) marked))

/-- Saturated Boolean form of `DTrSharp` over a finite transition system. -/
def markerTable (lts : CCS.FiniteLTS Action State) : MarkerTable State :=
  saturate (configs lts) configMem (fun marked config => marks lts marked config.1 config.2)

/-- Executable finite-state approximation of `AbstractDiff`. -/
def abstractDiff (lts : CCS.FiniteLTS Action State) (state : State)
    (competitors : StateSet State) : Bool :=
  configMem (state, competitors) (markerTable lts)

end FiniteLTS
end EqCheckingAbstractInterpretation.Trace
