import EqCheckingAbstractInterpretation.Trace.Basic

/-!
# Concrete Trace Difference Transformer

This file formalizes the "Concrete Trace Differences" subsection of the note
(Definition 2.6 and Proposition 2.7):

- `DiffSys`: the space of difference systems `DS = (CCS × ProcSet) → TraceSet`,
  ordered pointwise by subset inclusion.
- `DTr`: the concrete predecessor transformer `D_Tr : 𝒳 → 𝒳`, defined inductively
  on trace structure:
  - `[] ∈ D_Tr(ρ)(p, Q)`   iff   `Q = ∅`
  - `a::tr' ∈ D_Tr(ρ)(p, Q)`   iff   `∃ p' ∈ Der(p, a), tr' ∈ ρ(p', Der(Q, a))`
- `lfpDTr`: the least fixpoint of `DTr`, defined as the intersection of all
  pre-fixpoints (Knaster–Tarski / Kleene characterisation).
- `traceDifferenceToSet_eq_lfpDTr`: the main result, establishing
  `TraceDifferenceToSet env p Q = lfpDTr env p Q`.
-/

namespace EqCheckingAbstractInterpretation.Trace

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/-- A *difference system* maps each pair `(p, Q)` to a set of traces (Def 2.6 in the note). -/
abbrev DiffSys (Action : Type u) (Name : Type v) :=
  CCS Action Name → (CCS Action Name → Prop) → Trace Action → Prop

/-- Pointwise order on difference systems: `ρ ≤ σ` iff `ρ(p,Q) ⊆ σ(p,Q)` for all `(p,Q)`. -/
def DiffSysLe (ρ σ : DiffSys Action Name) : Prop :=
  ∀ p Q tr, ρ p Q tr → σ p Q tr

/--
The concrete predecessor transformer `D_Tr` (Definition 2.6).

`DTr env ρ p Q tr` is defined inductively on the structure of the trace `tr`:
- `tr = []` (the empty observation `⊤`): holds iff `Q = ∅`, because `⊤` is
  a distinguishing observation from the empty set of competitors.
- `tr = a :: tr'` (the prefixed observation `⟨a⟩tr'`): holds iff there exists a
  successor `p' ∈ Der(p, a)` such that `tr' ∈ ρ(p', Der(Q, a))`, propagating
  distinguishing observations backward along derivatives.
-/
def DTr (env : Env Action Name) (ρ : DiffSys Action Name)
    (p : CCS Action Name) (Q : CCS Action Name → Prop) : Trace Action → Prop :=
  fun tr => match tr with
  | []       => ∀ q, ¬ Q q
  | a :: tr' => ∃ p', Deriv env p a p' ∧ ρ p' (DerivSetOf env Q a) tr'

/-- `DTr env` is monotone in `ρ` with respect to `DiffSysLe`. -/
theorem dTr_mono (env : Env Action Name) {ρ σ : DiffSys Action Name}
    (hle : DiffSysLe ρ σ) (p : CCS Action Name) (Q : CCS Action Name → Prop) :
    ∀ tr, DTr env ρ p Q tr → DTr env σ p Q tr := by
  intro tr h
  match tr with
  | []       => exact h
  | a :: tr' =>
      obtain ⟨p', hDer, hρ⟩ := h
      exact ⟨p', hDer, hle _ _ _ hρ⟩

/--
The least fixpoint of `DTr env`, defined proof-theoretically as the intersection
of all pre-fixpoints.  Equivalently, by Knaster–Tarski, this coincides with the
least element `ρ` satisfying `D_Tr(ρ) ⊆ ρ`.
-/
def lfpDTr (env : Env Action Name) : DiffSys Action Name :=
  fun p Q tr =>
    ∀ ρ : DiffSys Action Name,
      (∀ p' Q' tr', DTr env ρ p' Q' tr' → ρ p' Q' tr') →
      ρ p Q tr

/-- `lfpDTr env` is a pre-fixpoint: `DTr env (lfpDTr env) ⊆ lfpDTr env`. -/
theorem lfpDTr_prefixpoint (env : Env Action Name) :
    ∀ p Q tr, DTr env (lfpDTr env) p Q tr → lfpDTr env p Q tr := by
  intro p Q tr hF ρ hρ
  match tr with
  | []       => exact hρ p Q [] hF
  | a :: tr' =>
      obtain ⟨p', hDer, hlfp⟩ := hF
      exact hρ p Q (a :: tr') ⟨p', hDer, hlfp ρ hρ⟩

/--
`TraceDifferenceToSet env` is a pre-fixpoint of `DTr env`.
This is the key step (Part 2, "least among pre-fixpoints") in the proof of
Proposition 2.7: any pre-fixpoint contains the concrete difference, so
`lfpDTr env ≤ TraceDifferenceToSet env`.
-/
theorem traceDiff_is_prefixpoint (env : Env Action Name) :
    ∀ p Q tr, DTr env (TraceDifferenceToSet env) p Q tr →
              TraceDifferenceToSet env p Q tr := by
  intro p Q tr hF
  match tr with
  | []       =>
      -- hF : ∀ q, ¬ Q q
      refine ⟨TraceSem.nil p, ?_⟩
      intro ⟨q, hQq, _⟩
      exact hF q hQq
  | a :: tr' =>
      -- hF : ∃ p', Deriv env p a p' ∧ TraceDifferenceToSet env p' (DerivSetOf env Q a) tr'
      obtain ⟨p', hDer, hDiff'⟩ := hF
      refine ⟨TraceSem.cons hDer hDiff'.1, ?_⟩
      intro ⟨q, hQq, hqTr⟩
      cases hqTr with
      | cons hDerQ hTailQ =>
          exact hDiff'.2 ⟨_, ⟨q, hQq, hDerQ⟩, hTailQ⟩

/--
Part 1 of the proof of Proposition 2.7: the concrete trace difference is contained
in every pre-fixpoint of `DTr env`, hence in `lfpDTr env`.

The proof uses `TraceSem.rec` with a motive that universally quantifies over `Q`,
so that the induction hypothesis applies to the shifted set `DerivSetOf env Q a`
in the cons case.
-/
theorem traceDiff_le_lfp (env : Env Action Name) :
    ∀ p Q tr, TraceDifferenceToSet env p Q tr → lfpDTr env p Q tr := by
  intro p Q tr hDiff
  obtain ⟨hTr, hNeg⟩ := hDiff
  revert Q
  refine TraceSem.rec
    (motive := fun p tr _ =>
      ∀ (Q : CCS Action Name → Prop),
        (¬ ∃ q, Q q ∧ TraceSem env q tr) →
        lfpDTr env p Q tr)
    ?nil ?cons hTr
  · -- Base case: tr = []
    intro p' Q hNeg ρ hρ
    apply hρ
    intro q hQq
    exact hNeg ⟨q, hQq, TraceSem.nil q⟩
  · -- Step case: tr = a :: tr'
    -- ih : ∀ Q, (¬ ∃ q, Q q ∧ TraceSem env q tr') → lfpDTr env p' Q tr'
    intro p' p'' a tr' hDer _hTail ih
    intro Q hNeg ρ hρ
    apply hρ
    have hNegNext : ¬ ∃ q', DerivSetOf env Q a q' ∧ TraceSem env q' tr' := by
      intro ⟨q', ⟨q, hQq, hDerQ⟩, hTailQ⟩
      exact hNeg ⟨q, hQq, TraceSem.cons hDerQ hTailQ⟩
    exact ⟨p'', hDer, ih (DerivSetOf env Q a) hNegNext ρ hρ⟩

/--
**Proposition 2.7**: The concrete trace difference equals the least fixpoint of `DTr`.

For all `p : CCS` and `Q : ProcSet` and `tr : Trace`:
```
  tr ∈ TraceDifferenceToSet env p Q  ↔  tr ∈ lfpDTr env p Q
```

**Proof sketch**:
- (⊆) `TraceDifferenceToSet ⊆ lfpDTr`: by induction on the derivation of
  `TraceSem env p tr`, with Q universally quantified in the motive so that
  the IH shifts Q to `DerivSetOf env Q a` in the cons step.
- (⊇) `lfpDTr ⊆ TraceDifferenceToSet`: by instantiating the universal
  quantifier in `lfpDTr` with `TraceDifferenceToSet env` and checking
  that it is a pre-fixpoint of `DTr env` (`traceDiff_is_prefixpoint`).
-/
theorem traceDifferenceToSet_eq_lfpDTr
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : CCS Action Name → Prop)
    (tr : Trace Action) :
    TraceDifferenceToSet env p Q tr ↔ lfpDTr env p Q tr := by
  constructor
  · exact traceDiff_le_lfp env p Q tr
  · intro hlfp
    exact hlfp _ (traceDiff_is_prefixpoint env)

/--
Corollary: trace preorder reduces to a fixpoint-emptiness check (Proposition 2.7).
```
  TracePreorder env p q  ↔  ¬ ∃ tr, lfpDTr env p (· = q) tr
```
-/
theorem tracePreorder_iff_lfp_empty
    (env : Env Action Name)
    (p q : CCS Action Name) :
    TracePreorder env p q ↔ ¬ ∃ tr, lfpDTr env p {q} tr := by
  constructor
  · intro hPre ⟨tr, hlfp⟩
    have hDiff := (traceDifferenceToSet_eq_lfpDTr env p {q} tr).mpr hlfp
    exact hDiff.2 ⟨q, rfl, hPre tr hDiff.1⟩
  · intro hNoWitness tr hTr
    classical
    have hnn : ¬ ¬ traceSetOf env q tr := by
      intro hNotQ
      have hDiff : TraceDifferenceToSet env p {q} tr := by
        refine ⟨hTr, ?_⟩
        intro hExists
        rcases hExists with ⟨r, hrq, hrTr⟩
        exact hNotQ (hrq ▸ hrTr)
      exact hNoWitness ⟨tr, (traceDifferenceToSet_eq_lfpDTr env p {q} tr).mp hDiff⟩
    exact Classical.not_not.mp hnn

end EqCheckingAbstractInterpretation.Trace
