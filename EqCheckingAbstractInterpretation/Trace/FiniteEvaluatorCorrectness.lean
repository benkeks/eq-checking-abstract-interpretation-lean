import EqCheckingAbstractInterpretation.Trace.FiniteEvaluator
import EqCheckingAbstractInterpretation.Trace.AbstractTransformer

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS

universe u v w

namespace FiniteLTS

variable {Action : Type u} {State : Type v}
  [BEq Action] [BEq State] [DecidableEq State]

/--
Certificate that the saturated finite marker table equals the Trace semantic
least fixed point for a realization of the finite transition system.
-/
structure AbstractDiffCorrect
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name) : Prop where
  realizes : CCS.FiniteLTS.Realizes lts env decode
  correct : ∀ state competitors,
    abstractDiff lts state competitors = true ↔
      AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors)

/-- Generic connection from a certified executable finite model to `AbstractDiff`. -/
theorem abstractDiff_correct
    {Name : Type w}
    (lts : CCS.FiniteLTS Action State)
    (env : Env Action Name)
    (decode : State → CCS Action Name)
    (certificate : AbstractDiffCorrect lts env decode)
    (state : State)
    (competitors : StateSet State) :
    abstractDiff lts state competitors = true ↔
      AbstractDiff env (decode state) (CCS.FiniteLTS.decodeSet decode competitors) :=
  certificate.correct state competitors

end FiniteLTS
end EqCheckingAbstractInterpretation.Trace
