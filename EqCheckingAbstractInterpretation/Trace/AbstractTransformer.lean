import EqCheckingAbstractInterpretation.Trace.ConcreteTransformer

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/-- Property abstraction to non-emptiness on trace sets. -/
def alphaNonempty (S : Trace Action → Prop) : Prop :=
  ∃ tr, S tr

/-- Property concretization from non-emptiness back to a trace set. -/
def gammaNonempty (a : Prop) : Trace Action → Prop :=
  fun _ => a

/-- Pointwise lifting of `alphaNonempty` to difference systems. -/
def alphaDiffSys (ρc : DiffSys Action Name) :
    CCS Action Name → ProcSet Action Name → Prop :=
  fun p Q => alphaNonempty (ρc p Q)

/-- Pointwise lifting of `gammaNonempty` to difference systems. -/
def gammaDiffSys
    (ρa : CCS Action Name → ProcSet Action Name → Prop) :
    DiffSys Action Name :=
  fun p Q tr => gammaNonempty (ρa p Q) tr

/--
Abstract transformer for the non-emptiness property, defined explicitly by cases
matching the paper's @def-trace-abstract-interpretation:
- yield the marker if `Q = ∅`;
- otherwise propagate markers through action-successors.
This coincides with `α ∘ DTr ∘ γ` (see `DTrSharp_eq_alpha_comp_DTr_comp_gamma`).
-/
def DTrSharp
    (ρ : Env Action Name)
    (ρa : CCS Action Name → ProcSet Action Name → Prop) :
    CCS Action Name → ProcSet Action Name → Prop :=
  fun p Q =>
    (∀ q, ¬ Q q) ∨ ∃ a p', Deriv ρ p a p' ∧ ρa p' (DerivSetOf ρ Q a)

/-- Abstract difference systems for the non-emptiness abstraction. -/
abbrev AbsDiffSys (Action : Type u) (Name : Type v) :=
  CCS Action Name → ProcSet Action Name → Prop

/-- Least fixpoint of `DTrSharp`, defined as intersection of all pre-fixpoints. -/
def lfpDTrSharp
    (ρ : Env Action Name) :
    AbsDiffSys Action Name :=
  fun p Q =>
    ∀ ρa : AbsDiffSys Action Name,
      (∀ p' Q', DTrSharp ρ ρa p' Q' → ρa p' Q') →
      ρa p Q

/-- Abstract trace difference from the paper, defined as `lfp(DTrSharp)`. -/
abbrev AbstractDiff
    (ρ : Env Action Name) :
    AbsDiffSys Action Name :=
  lfpDTrSharp ρ

/-- Marker-based failure of trace preorder against a singleton right-hand process. -/
def MarkerFailsPreorder
    (ρ : Env Action Name) (p q : CCS Action Name) : Prop :=
  AbstractDiff ρ p {q}

/-- `lfpDTrSharp` is a pre-fixpoint of `DTrSharp`. -/
theorem lfpDTrSharp_prefixpoint
    (ρ : Env Action Name) :
    ∀ p Q, DTrSharp ρ (lfpDTrSharp ρ) p Q → lfpDTrSharp ρ p Q := by
  intro p Q h ρa hρa
  apply hρa
  unfold DTrSharp at h ⊢
  rcases h with hBase | ⟨a, p', hDer, hNext⟩
  · exact Or.inl hBase
  · exact Or.inr ⟨a, p', hDer, hNext ρa hρa⟩

theorem abstractDiff_empty (ρ : Env Action Name) (p : CCS Action Name) :
    AbstractDiff ρ p ∅ := by
  show lfpDTrSharp ρ p ∅
  apply lfpDTrSharp_prefixpoint ρ p ∅
  exact Or.inl (fun q hQ => hQ)

end EqCheckingAbstractInterpretation.Trace
