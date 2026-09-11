import EqCheckingAbstractInterpretation.CCS.Basic
import Mathlib.Data.Finset.Basic

namespace EqCheckingAbstractInterpretation.CCS

universe u v w

/-- A finite, executable labelled transition system. -/
structure FiniteLTS (Action : Type u) (State : Type v) [DecidableEq Action] [DecidableEq State] where
  actions : List Action
  states : List State
  next : State → Action → List State

namespace FiniteLTS

variable {Action : Type u} {State : Type v} [DecidableEq Action] [DecidableEq State]

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
  next_sound : ∀ state action target,
    target ∈ lts.next state action → Deriv env (decode state) action (decode target)
  next_closed : ∀ state action target,
    state ∈ lts.states → target ∈ lts.next state action → target ∈ lts.states
  next_complete : ∀ state action process,
    state ∈ lts.states → Deriv env (decode state) action process →
      ∃ target, target ∈ lts.states ∧ target ∈ lts.next state action ∧
        decode target = process

/-- Interpret a finite competitor list as a predicate on decoded CCS processes. -/
def decodeSet {Name : Type w} [DecidableEq State] (decode : State → CCS Action Name)
  (competitors : Finset State) : ProcSet Action Name :=
  fun process => ∃ state, state ∈ competitors ∧ decode state = process

end FiniteLTS
end EqCheckingAbstractInterpretation.CCS
