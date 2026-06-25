import EqCheckingAbstractInterpretation.Trace.Correctness

namespace EqCheckingAbstractInterpretation.Trace.RunningExample

open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.Trace

/-!
## Running Example: Abstract Trace Differences

This file formalizes the running example for abstract trace differences.
We instantiate the abstract difference computation `AbstractDiff` for the
example with processes:

  `PA  = a.PA + a.b.0`    (the `P_A` of the note)
  `PB  = a.(PB + b.0)`    (the `P_B` of the note)
  `PBb0 = PB + b.0`       (the reachable intermediate state)
  `b0  = b.0`             (the stopping process)

Key results:
1. `abstractDiff_PBb0_b0`     : marker present for `(PBb0, {b0})`  → not-preordered
2. `not_abstractDiff_b0_PBb0` : marker absent for `(b0, {PBb0})`   → b0 ≤ PBb0
3. `not_abstractDiff_PA_PB`   : marker absent for `(PA,  {PB})`    → PA ≡ PB
-/

/-- Actions: `a` and `b`. -/
inductive RunAct where
  | a
  | b
  deriving DecidableEq

/-- Process names: `PA` and `PB`. -/
inductive RunName where
  | PA
  | PB
  deriving DecidableEq

abbrev RunProc := CCS RunAct RunName

/-- Environment:
  `PA ↦ a.PA + a.b.0`
  `PB ↦ a.(PB + b.0)` -/
def runEnv : Env RunAct RunName
  | .PA => .choice (.prefix .a (.var .PA)) (.prefix .a (.prefix .b .zero))
  | .PB => .prefix .a (.choice (.var .PB) (.prefix .b .zero))

def PA   : RunProc := .var .PA
def PB   : RunProc := .var .PB
def b0   : RunProc := .prefix .b .zero
def PBb0 : RunProc := .choice (.var .PB) (.prefix .b .zero)

-- ---------------------------------------------------------------------------
-- Derivative lemmas
-- ---------------------------------------------------------------------------

/-- `b.0` has no `a`-derivative. -/
theorem b0_no_a_deriv (p : RunProc) : ¬ Deriv runEnv b0 RunAct.a p := by
  intro h; cases h

/-- The `a`-shifted set of `{b.0}` is empty: `b.0` has no `a`-derivative. -/
theorem derivSetOf_b0_a_empty :
    DerivSetOf runEnv {b0} RunAct.a = (fun _ => False) := by
  funext p; apply propext
  exact ⟨fun ⟨_, hq, hDer⟩ => by subst hq; exact b0_no_a_deriv p hDer, False.elim⟩

-- ---------------------------------------------------------------------------
-- 1. Positive: PBb0 can be distinguished from b0
-- ---------------------------------------------------------------------------

/-- Abstract trace difference is present for `(PBb0, {b0})`.

    Derivation (two-step lfp construction):
    - `step`: `PBb0 --a--> PBb0`, shifted set `Der({b.0}, a) = ∅`
    - `base`: the empty competitor set triggers the base case of `DTrSharp`. -/
theorem abstractDiff_PBb0_b0 :
    AbstractDiff runEnv PBb0 {b0} := by
  show lfpDTrSharp runEnv PBb0 {b0}
  apply lfpDTrSharp_prefixpoint runEnv PBb0 {b0}
  refine Or.inr ?_
  refine ⟨.a, PBb0, Deriv.choice_left (Deriv.var Deriv.prefix), ?_⟩
  rw [derivSetOf_b0_a_empty]
  exact abstractDiff_empty runEnv PBb0

-- ---------------------------------------------------------------------------
-- 2. Negative: b0 is trace-preordered below PBb0
-- ---------------------------------------------------------------------------

/-- Every trace of `b0` is also a trace of `PBb0`:
    `b0 = b.0` can only do `b` to `0`, and `PBb0 = PB + b.0` can also do `b` to `0`. -/
theorem b0_le_PBb0 : TracePreorder runEnv b0 PBb0 := by
  intro tr htr
  generalize hb : b0 = bz at htr
  induction htr with
  | nil => exact TraceSem.nil _
  | cons hDer hNext ih =>
    subst hb; cases hDer
    cases hNext with
    | nil => exact TraceSem.cons (Deriv.choice_right Deriv.prefix) (TraceSem.nil _)
    | cons hDer2 _ => exact absurd hDer2 (by intro h; cases h)

/-- Abstract trace difference is absent for `(b0, {PBb0})`.

    `b0` is concrete-trace preordered below `PBb0` (every trace of `b0` is
    a trace of `PBb0`), so the marker can never appear. -/
theorem not_abstractDiff_b0_PBb0 :
    ¬ AbstractDiff runEnv b0 {PBb0} := by
  rw [markerPresence_iff_concreteDiffNonempty]
  intro ⟨tr, htr, hNot⟩
  exact hNot ⟨PBb0, rfl, b0_le_PBb0 tr htr⟩

-- ---------------------------------------------------------------------------
-- 3. Negative: PA and PB are trace-equivalent (no abstract difference)
-- ---------------------------------------------------------------------------

/-- Every trace of `PA` is also a trace of `PB`.

    Proved by simultaneous induction on `TraceSem`: for every reachable
    successor state `p` of `PA` (i.e. `p ∈ {PA, b0, zero}`), every trace
    of `p` is also a trace of the corresponding `PB`-side state. -/
theorem PA_le_PB : TracePreorder runEnv PA PB := by
  intro tr htr
  have key : ∀ p tr', TraceSem runEnv p tr' →
      (p = PA → TraceSem runEnv PBb0 tr' ∧ TraceSem runEnv PB tr') ∧
      (p = b0 → TraceSem runEnv PBb0 tr') ∧
      (p = (CCS.zero : RunProc) → tr' = []) := by
    intro p tr' h
    induction h with
    | nil =>
      exact ⟨fun _ => ⟨TraceSem.nil _, TraceSem.nil _⟩,
             fun _ => TraceSem.nil _,
             fun _ => rfl⟩
    | cons hDer hNext ih =>
      refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
      · subst heq
        cases hDer with
        | var hInner =>
          simp only [runEnv] at hInner
          cases hInner with
          | choice_left hPA =>
            cases hPA
            obtain ⟨hPBb0, hPB⟩ := ih.1 rfl
            exact ⟨TraceSem.cons (Deriv.choice_left (Deriv.var Deriv.prefix)) hPBb0,
                   TraceSem.cons (Deriv.var Deriv.prefix) hPBb0⟩
          | choice_right hb =>
            cases hb
            obtain hPBb0 := ih.2.1 rfl
            exact ⟨TraceSem.cons (Deriv.choice_left (Deriv.var Deriv.prefix)) hPBb0,
                   TraceSem.cons (Deriv.var Deriv.prefix) hPBb0⟩
      · subst heq; cases hDer
        obtain heq := ih.2.2 rfl; subst heq
        exact TraceSem.cons (Deriv.choice_right Deriv.prefix) (TraceSem.nil _)
      · subst heq; exact absurd hDer (by intro h; cases h)
  exact (key PA tr htr).1 rfl |>.2

/-- Abstract trace difference is absent for `(PA, {PB})`.

    `PA` and `PB` have identical trace languages
    (`{a^n | n ≥ 0} ∪ {a^n b | n ≥ 1}`), so `PA ≤_Tr PB` and no
    abstract difference marker can be derived. -/
theorem not_abstractDiff_PA_PB :
    ¬ AbstractDiff runEnv PA {PB} := by
  rw [markerPresence_iff_concreteDiffNonempty]
  intro ⟨tr, htr, hNot⟩
  exact hNot ⟨PB, rfl, PA_le_PB tr htr⟩

end EqCheckingAbstractInterpretation.Trace.RunningExample
