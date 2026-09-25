import EqCheckingAbstractInterpretation

open EqCheckingAbstractInterpretation
open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.Trace

structure Transition where
  source : Nat
  target : Nat
  label : String

private def parseState (lineNumber : Nat) (fieldName value : String) : Except String Nat :=
  let value := value.trimAscii.toString
  match value.toNat? with
  | some state => .ok state
  | none => .error s!"line {lineNumber}: invalid {fieldName} state ID '{value}'"

private def parseTransition (lineNumber : Nat) (line : String) : Except String Transition := do
  match line.splitOn "," with
  | [source, target, label] =>
    let source <- parseState lineNumber "source" source
    let target <- parseState lineNumber "target" target
    let label := label.trimAscii.toString
    if label.isEmpty then
      throw s!"line {lineNumber}: transition label must not be empty"
    else
      pure { source, target, label }
  | _ => throw s!"line {lineNumber}: expected exactly three comma-separated fields"

private def parseLines : Nat → List String → Except String (List Transition)
  | _, [] => .ok []
  | lineNumber, line :: lines => do
    let transitions <- parseLines (lineNumber + 1) lines
    if line.trimAscii.toString.isEmpty then
      pure transitions
    else
      pure ((← parseTransition lineNumber line) :: transitions)

private def parseTransitions (contents : String) : Except String (List Transition) :=
  parseLines 1 (contents.splitOn "\n")

private def toLTS (transitions : List Transition) : FiniteLTS String Nat :=
  let states := (transitions.flatMap (fun transition => [transition.source, transition.target])).eraseDups
  let actions := (transitions.map Transition.label).eraseDups
  { states
    actions
    next := fun state action =>
      (transitions.filter (fun transition => transition.source == state && transition.label == action)
        ).map Transition.target }

private def preorderName : Ready.Capability → String
  | .T => "trace"
  | .S => "simulation"
  | .F => "failures"
  | .RS => "ready simulation"

private def holdingReadyPreorders (lts : FiniteLTS String Nat) (left right : Nat) : List String :=
  let minimal := Ready.FiniteLTS.readyCapabilities lts left {right}
  (Ready.FiniteLTS.capabilities.filter (fun threshold =>
    !minimal.any (fun requirement => Ready.FiniteLTS.capLeBool requirement threshold))).map preorderName

private def usage : String :=
  "Usage: Main <trace|ready> <transitions.csv> <left-state-id> <right-state-id>"

private def run (mode csvPath leftStateText rightStateText : String) : IO Unit := do
  match String.toNat? leftStateText, String.toNat? rightStateText with
  | some leftState, some rightState =>
    try
      match parseTransitions (← IO.FS.readFile csvPath) with
      | .error message => IO.eprintln s!"CSV parse error: {message}"
      | .ok transitions =>
        let lts := toLTS transitions
        if !lts.states.contains leftState then
          IO.eprintln s!"Input error: state ID {leftState} does not occur in the transition system"
        else if !lts.states.contains rightState then
          IO.eprintln s!"Input error: state ID {rightState} does not occur in the transition system"
        else if mode == "trace" then
          IO.println s!"tracePreordered({leftState}, {rightState}) = {FiniteLTS.tracePreordered lts leftState rightState}"
        else
          let preorders := holdingReadyPreorders lts leftState rightState
          let names := if preorders.isEmpty then "none" else String.intercalate ", " preorders
          IO.println s!"Holding preorders for ({leftState}, {rightState}): {names}"
    catch exception =>
      IO.eprintln s!"Unable to read '{csvPath}': {exception}"
  | _, _ => IO.eprintln "Input error: state IDs must be non-negative integers"

def main (args : List String) : IO Unit := do
  match args with
  | ["trace", csvPath, leftStateText, rightStateText] =>
    run "trace" csvPath leftStateText rightStateText
  | ["ready", csvPath, leftStateText, rightStateText] =>
    run "ready" csvPath leftStateText rightStateText
  | [mode, _, _, _] => IO.eprintln s!"Input error: unknown mode '{mode}' (expected trace or ready)"
  | _ => IO.eprintln usage
