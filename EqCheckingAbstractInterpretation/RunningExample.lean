import EqCheckingAbstractInterpretation.CCS.FiniteLTS

namespace EqCheckingAbstractInterpretation.RunningExample

open EqCheckingAbstractInterpretation.CCS

set_option linter.constructorNameAsVariable false

/-- Actions in the running example. -/
inductive RunAct where
  | a
  | b
  deriving DecidableEq, Repr

/-- Process names in the running example. -/
inductive RunName where
  | PA
  | PB
  deriving DecidableEq, Repr

abbrev RunProc := CCS RunAct RunName

def PA : RunProc := .var .PA
def PB : RunProc := .var .PB
def b0 : RunProc := .prefix .b .zero
def PBb0 : RunProc := .choice (.var .PB) (.prefix .b .zero)

/-- `PA ↦ a.PA + a.b.0`, `PB ↦ a.(PB + b.0)`. -/
def runEnv : Env RunAct RunName
  | .PA => .choice (.prefix .a (.var .PA)) (.prefix .a (.prefix .b .zero))
  | .PB => .prefix .a (.choice (.var .PB) (.prefix .b .zero))

/-- The finite transition table induced by `runEnv`. -/
def runNext : RunProc → RunAct → List RunProc
  | .var .PA, .a => [PA, b0]
  | .var .PB, .a => [PBb0]
  | .choice (.var .PB) (.prefix .b .zero), .a => [PBb0]
  | .choice (.var .PB) (.prefix .b .zero), .b => [.zero]
  | .prefix .b .zero, .b => [.zero]
  | _, _ => []

/-- The derivative-closed finite fragment induced by `runEnv`. -/
def runLTS : CCS.FiniteLTS RunAct RunProc where
  actions := [.a, .b]
  states := [PA, PB, PBb0, b0, .zero]
  next := runNext

end EqCheckingAbstractInterpretation.RunningExample
