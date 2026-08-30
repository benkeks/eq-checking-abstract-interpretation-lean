import EqCheckingAbstractInterpretation.CCS.Basic

namespace EqCheckingAbstractInterpretation.CCS

universe u v w

/-- A finite, executable labelled transition system. -/
structure FiniteLTS (Action : Type u) (State : Type v) [BEq Action] [BEq State] where
  actions : List Action
  states : List State
  next : State → Action → List State

namespace FiniteLTS

variable {Action : Type u} {State : Type v} [BEq Action] [BEq State]

/--
A finite transition system realizes a CCS environment when its transition table
enumerates exactly the derivatives of the represented processes.
-/
structure Realizes
    {Name : Type w}
    (lts : FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name) : Prop where
  actions_nodup : lts.actions.Nodup
  states_nodup : lts.states.Nodup
  action_complete : ∀ action, action ∈ lts.actions
  state_complete : ∀ state, state ∈ lts.states
  next_correct : ∀ state action target,
    target ∈ lts.next state action ↔ Deriv env (decode state) action (decode target)

/-- Interpret a finite competitor list as a predicate on decoded CCS processes. -/
def decodeSet {Name : Type w} (decode : State → CCS Action Name)
    (competitors : List State) : ProcSet Action Name :=
  fun process => ∃ state, state ∈ competitors ∧ decode state = process

end FiniteLTS
end EqCheckingAbstractInterpretation.CCS
