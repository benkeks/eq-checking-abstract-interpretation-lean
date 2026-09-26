import EqCheckingAbstractInterpretation

open EqCheckingAbstractInterpretation
open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.Trace

structure Transition where
  source : Nat
  target : Nat
  label : String

structure StateName where
  state : Nat
  name : String
  annotation : String

structure ParsedLTS where
  transitions : List Transition
  names : List StateName

private def parseState (lineNumber : Nat) (fieldName value : String) : Except String Nat :=
  let value := value.trimAscii.toString
  match value.toNat? with
  | some state => .ok state
  | none => .error s!"line {lineNumber}: invalid {fieldName} state ID '{value}'"

private def parseRow (lineNumber : Nat) (line : String) : Except String (Sum Transition StateName) := do
  match line.splitOn "," with
  | [source, targetText, label] =>
    let source <- parseState lineNumber "source" source
    let targetText := targetText.trimAscii.toString
    let label := label.trimAscii.toString
    match targetText.toNat? with
    | some target =>
      if label.isEmpty then
        throw s!"line {lineNumber}: transition label must not be empty"
      else
        pure (.inl { source, target, label })
    | none =>
      if !targetText.toList.any Char.isAlpha then
        throw s!"line {lineNumber}: invalid target state ID or name '{targetText}'"
      else
        pure (.inr { state := source, name := targetText, annotation := label })
  | _ => throw s!"line {lineNumber}: expected exactly three comma-separated fields"

private def parseLines (lineNumber : Nat) (parsed : ParsedLTS) : List String → Except String ParsedLTS
  | [] => .ok { transitions := parsed.transitions.reverse, names := parsed.names.reverse }
  | line :: lines => do
    if line.trimAscii.toString.isEmpty then
      parseLines (lineNumber + 1) parsed lines
    else
      match ← parseRow lineNumber line with
      | .inl transition =>
        parseLines (lineNumber + 1) { parsed with transitions := transition :: parsed.transitions } lines
      | .inr entry =>
        if parsed.names.any (fun name => name.name == entry.name) then
          throw s!"line {lineNumber}: duplicate state name '{entry.name}'"
        else
          parseLines (lineNumber + 1) { parsed with names := entry :: parsed.names } lines

private def parseTransitions (contents : String) : Except String ParsedLTS :=
  parseLines 1 { transitions := [], names := [] } (contents.splitOn "\n")

private def toLTS (parsed : ParsedLTS) : FiniteLTS String Nat :=
  let states := ((parsed.transitions.flatMap (fun transition => [transition.source, transition.target])) ++
    parsed.names.map StateName.state).eraseDups
  let actions := (parsed.transitions.map Transition.label).eraseDups
  let successors := parsed.transitions.foldr (fun transition (lookup : Std.HashMap (Nat × String) (List Nat)) =>
    let key := (transition.source, transition.label)
    lookup.insert key (transition.target :: lookup.getD key [])) {}
  { states
    actions
    next := fun state action => successors.getD (state, action) [] }

private def resolveState (parsed : ParsedLTS) (text : String) : Except String Nat :=
  match text.toNat? with
  | some state => .ok state
  | none =>
    match parsed.names.find? (fun entry => entry.name == text) with
    | some entry => .ok entry.state
    | none => .error s!"Input error: unknown state name '{text}'"

private def preorderName : Ready.Capability → String
  | .T => "trace"
  | .S => "simulation"
  | .F => "failures"
  | .RS => "ready-simulation"

private def holdingReadyPreorders (lts : FiniteLTS String Nat) (left right : Nat) : List String :=
  let minimal := Ready.FiniteLTS.readyCapabilities lts left {right}
  (Ready.FiniteLTS.capabilities.filter (fun threshold =>
    !minimal.any (fun requirement => Ready.FiniteLTS.capLeBool requirement threshold))).map preorderName

private def usage : String :=
  "Usage: Main <trace|ready> <transitions.csv> <left-state> <right-state>"

private def run (mode csvPath leftStateText rightStateText : String) : IO Unit := do
  try
    match parseTransitions (← IO.FS.readFile csvPath) with
    | .error message => IO.eprintln s!"CSV parse error: {message}"
    | .ok parsed =>
      match resolveState parsed leftStateText, resolveState parsed rightStateText with
      | .error message, _ => IO.eprintln message
      | _, .error message => IO.eprintln message
      | .ok leftState, .ok rightState =>
        let lts := toLTS parsed
        if !lts.states.contains leftState then
          IO.eprintln s!"Input error: state ID {leftState} does not occur in the transition system"
        else if !lts.states.contains rightState then
          IO.eprintln s!"Input error: state ID {rightState} does not occur in the transition system"
        else if mode == "trace" then
          IO.println s!"tracePreordered({leftStateText}, {rightStateText}) = {FiniteLTS.tracePreordered lts leftState rightState}"
        else
          let preorders := holdingReadyPreorders lts leftState rightState
          let names := if preorders.isEmpty then "none" else String.intercalate ", " preorders
          IO.println s!"Holding preorders for ({leftStateText}, {rightStateText}): {names}"
  catch exception =>
    IO.eprintln s!"Unable to read '{csvPath}': {exception}"

def main (args : List String) : IO Unit := do
  match args with
  | ["trace", csvPath, leftStateText, rightStateText] =>
    run "trace" csvPath leftStateText rightStateText
  | ["ready", csvPath, leftStateText, rightStateText] =>
    run "ready" csvPath leftStateText rightStateText
  | [mode, _, _, _] => IO.eprintln s!"Input error: unknown mode '{mode}' (expected trace or ready)"
  | _ => IO.eprintln usage
