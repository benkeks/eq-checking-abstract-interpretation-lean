import EqCheckingAbstractInterpretation.CCS.Basic

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/-- A trace is a finite sequence of actions. -/
abbrev Trace (Action : Type u) := List Action

/-- A trace set is a predicate on traces. -/
abbrev TraceSet (Action : Type u) := Trace Action → Prop

inductive TraceSem (ρ : Env Action Name) : CCS Action Name → Trace Action → Prop where
  | nil (p) : TraceSem ρ p []
  | cons {p p' a tr} : Deriv ρ p a p' → TraceSem ρ p' tr → TraceSem ρ p (a :: tr)

def traceSetOf (ρ : Env Action Name) (p : CCS Action Name) : TraceSet Action :=
  fun tr => TraceSem ρ p tr

def TraceDifference (ρ : Env Action Name) (p q : CCS Action Name) : TraceSet Action :=
  fun tr => traceSetOf ρ p tr ∧ ¬ traceSetOf ρ q tr

def TraceDifferenceToSet
    (ρ : Env Action Name)
    (p : CCS Action Name)
    (Q : CCS Action Name → Prop) : TraceSet Action :=
  fun tr => traceSetOf ρ p tr ∧ ¬ ∃ q, Q q ∧ traceSetOf ρ q tr

def TracePreorder
    (ρ : Env Action Name) (p q : CCS Action Name) : Prop :=
  ∀ tr, traceSetOf ρ p tr → traceSetOf ρ q tr

def TraceEquivalent
    (ρ : Env Action Name) (p q : CCS Action Name) : Prop :=
  TracePreorder ρ p q ∧ TracePreorder ρ q p

theorem tracePreorder_refl (ρ : Env Action Name) (p : CCS Action Name) :
    TracePreorder ρ p p := by
  intro tr htr
  exact htr

theorem tracePreorder_trans
    (ρ : Env Action Name) (p₁ p₂ p₃ : CCS Action Name)
    (h₁₂ : TracePreorder ρ p₁ p₂)
    (h₂₃ : TracePreorder ρ p₂ p₃) :
    TracePreorder ρ p₁ p₃ := by
  intro tr htr
  exact h₂₃ tr (h₁₂ tr htr)

theorem traceEquivalent_refl (ρ : Env Action Name) (p : CCS Action Name) :
    TraceEquivalent ρ p p := by
  exact ⟨tracePreorder_refl ρ p, tracePreorder_refl ρ p⟩

theorem traceEquivalent_symm
    (ρ : Env Action Name) (p q : CCS Action Name) :
    TraceEquivalent ρ p q → TraceEquivalent ρ q p := by
  intro h
  exact ⟨h.2, h.1⟩

theorem traceEquivalent_trans
    (ρ : Env Action Name) (p₁ p₂ p₃ : CCS Action Name)
    (h₁₂ : TraceEquivalent ρ p₁ p₂)
    (h₂₃ : TraceEquivalent ρ p₂ p₃) :
    TraceEquivalent ρ p₁ p₃ := by
  refine ⟨?_, ?_⟩
  · exact tracePreorder_trans ρ p₁ p₂ p₃ h₁₂.1 h₂₃.1
  · exact tracePreorder_trans ρ p₃ p₂ p₁ h₂₃.2 h₁₂.2

theorem tracePreorder_iff_noDifference
    (ρ : Env Action Name) (p q : CCS Action Name) :
    TracePreorder ρ p q ↔ ∀ tr, ¬ TraceDifference ρ p q tr := by
  constructor
  · intro hpre tr hdiff
    exact hdiff.2 (hpre tr hdiff.1)
  · intro h tr htr
    classical
    have hnn : ¬ ¬ traceSetOf ρ q tr := by
      intro hnot
      exact h tr ⟨htr, hnot⟩
    exact Classical.not_not.mp hnn

theorem traceDifferenceToSet_singleton
    (ρ : Env Action Name) (p q : CCS Action Name) (tr : Trace Action) :
    TraceDifferenceToSet ρ p {q} tr ↔ TraceDifference ρ p q tr := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro hq
    exact h.2 ⟨q, rfl, hq⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro hq
    rcases hq with ⟨r, hr, hrtr⟩
    cases hr
    exact h.2 hrtr

end EqCheckingAbstractInterpretation.Trace
