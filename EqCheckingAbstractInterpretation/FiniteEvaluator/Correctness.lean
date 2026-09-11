import EqCheckingAbstractInterpretation.FiniteEvaluator.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.FixedPoints

namespace EqCheckingAbstractInterpretation.FiniteEvaluator

universe u

variable {Element : Type u} [DecidableEq Element]

/-- Proof-facing inflationary extension of a finite-domain marker table. -/
def tableStep
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (marked : Set Config) : Set Config :=
    marked ∪ { config | config ∈ domain ∧ marks marked config }

/-- The table extension is monotone whenever the marker relation is monotone. -/
def tableStepHom
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (hMarksMono : ∀ {left right}, left ⊆ right → ∀ config,
            marks left config → marks right config) :
        Set Config →o Set Config where
    toFun := tableStep domain marks
    monotone' := by
        intro left right hSubset config hMarked
        rcases hMarked with hMarked | ⟨hDomain, hMarks⟩
        · exact Or.inl (hSubset hMarked)
        · exact Or.inr ⟨hDomain, hMarksMono hSubset config hMarks⟩

/-- The least marker table induced by a monotone finite-domain marker relation. -/
def tableLfp
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (hMarksMono : ∀ {left right}, left ⊆ right → ∀ config,
            marks left config → marks right config) : Set Config :=
    (tableStepHom domain marks hMarksMono).lfp

/-- The Mathlib least marker table is a fixed point of the inflationary extension. -/
theorem tableStep_tableLfp
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (hMarksMono : ∀ {left right}, left ⊆ right → ∀ config,
            marks left config → marks right config) :
        tableStep domain marks (tableLfp domain marks hMarksMono) =
            tableLfp domain marks hMarksMono := by
    exact (tableStepHom domain marks hMarksMono).map_lfp

/-- Any pre-fixed marker table contains the Mathlib least marker table. -/
theorem tableLfp_subset_of_prefixed
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (hMarksMono : ∀ {left right}, left ⊆ right → ∀ config,
            marks left config → marks right config)
        (marked : Set Config)
        (hPrefixed : tableStep domain marks marked ⊆ marked) :
        tableLfp domain marks hMarksMono ⊆ marked := by
    exact (tableStepHom domain marks hMarksMono).lfp_le hPrefixed

/--
One executable saturation pass denotes the proof-facing `tableStep` whenever
the Boolean membership and marking tests reflect their propositional forms.
-/
theorem saturateStep_toFinset
        {Config : Type u} [DecidableEq Config]
        (configs marked : List Config)
        (contains : Config → List Config → Bool)
        (marks : List Config → Config → Bool)
        (marksSet : Set Config → Config → Prop)
        (hContains : ∀ config marked, contains config marked = true ↔ config ∈ marked)
        (hMarks : ∀ marked config,
            marks marked config = true ↔ marksSet (marked.toFinset : Set Config) config) :
        ((saturateStep configs contains marks marked).toFinset : Set Config) =
            tableStep (configs.toFinset : Set Config) marksSet (marked.toFinset : Set Config) := by
    ext config
    change config ∈ (saturateStep configs contains marks marked).toFinset ↔
        config ∈ marked.toFinset ∨
            (config ∈ configs.toFinset ∧ marksSet (marked.toFinset : Set Config) config)
    simp only [saturateStep, List.mem_toFinset, List.mem_append, List.mem_filter,
        Bool.and_eq_true]
    exact ⟨
        fun h => Or.elim h
            (fun hMarked => Or.inl hMarked)
            (fun hFilter => Or.inr ⟨hFilter.1, (hMarks marked config).mp hFilter.2.2⟩),
        fun h => Or.elim h
            (fun hMarked => Or.inl hMarked)
            (fun hMarked => if hContained : config ∈ marked then
                Or.inl hContained
            else
                Or.inr ⟨hMarked.1, ⟨by
                    cases hContainsValue : contains config marked with
                    | false => rfl
                    | true => exact False.elim (hContained ((hContains config marked).mp hContainsValue)),
                    (hMarks marked config).mpr hMarked.2⟩⟩)⟩

/-- The proof-facing approximation after a fixed number of marker-table rounds. -/
def tableIter
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop) : Nat → Set Config
    | 0 => ∅
    | count + 1 => tableStep domain marks (tableIter domain marks count)

/-- Every table approximation is contained in its finite configuration domain. -/
theorem tableIter_subset_domain
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (count : Nat) :
        tableIter domain marks count ⊆ domain := by
    induction count with
    | zero => simp [tableIter]
    | succ count ih =>
        intro config hConfig
        rcases hConfig with hConfig | ⟨hDomain, _⟩
        · exact ih hConfig
        · exact hDomain

/-- Table iteration is inflationary at every round. -/
theorem tableIter_subset_succ
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (count : Nat) :
        tableIter domain marks count ⊆ tableIter domain marks (count + 1) := by
    intro config hConfig
    exact Or.inl hConfig

/-- A pre-fixed iteration remains unchanged in all later rounds. -/
theorem tableIter_add_eq_of_prefixed
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (count : Nat)
        (hPrefixed : tableStep domain marks (tableIter domain marks count) ⊆
            tableIter domain marks count)
        (extra : Nat) :
        tableIter domain marks (count + extra) = tableIter domain marks count := by
    have hFixed : tableStep domain marks (tableIter domain marks count) =
        tableIter domain marks count := Set.Subset.antisymm hPrefixed (fun _ h => Or.inl h)
    induction extra with
    | zero => rfl
    | succ extra ih =>
        calc
            tableIter domain marks (count + (extra + 1)) =
                tableStep domain marks (tableIter domain marks (count + extra)) := by
                  rw [Nat.add_succ]
                  rfl
            _ = tableStep domain marks (tableIter domain marks count) := by rw [ih]
            _ = tableIter domain marks count := hFixed

/-- A non-pre-fixed round strictly enlarges the marker table. -/
theorem tableIter_ssubset_succ_of_not_prefixed
                {Config : Type u}
                (domain : Set Config)
                (marks : Set Config → Config → Prop)
                (count : Nat)
                (hNotPrefixed : ¬ tableStep domain marks (tableIter domain marks count) ⊆
                        tableIter domain marks count) :
                tableIter domain marks count ⊂ tableIter domain marks (count + 1) := by
        refine (ssubset_iff_subset_ne).mpr ⟨tableIter_subset_succ domain marks count, ?_⟩
        intro hEqual
        apply hNotPrefixed
        have hFixed : tableStep domain marks (tableIter domain marks count) =
                tableIter domain marks count := by
            simpa only [tableIter] using hEqual.symm
        exact hFixed.subset

/-- Inflationary iteration over a finite domain reaches a pre-fixed table by its cardinality. -/
theorem tableIter_prefixed_at_card
                {Config : Type u}
                (domain : Finset Config)
                (marks : Set Config → Config → Prop) :
                tableStep (domain : Set Config) marks
                    (tableIter (domain : Set Config) marks domain.card) ⊆
                        tableIter (domain : Set Config) marks domain.card := by
        by_contra hNotPrefixed
        have hNoPrefixed : ∀ count, count ≤ domain.card →
                ¬ tableStep (domain : Set Config) marks (tableIter (domain : Set Config) marks count) ⊆
                        tableIter (domain : Set Config) marks count := by
            intro count hCount hPrefixed
            apply hNotPrefixed
            have hEqual := tableIter_add_eq_of_prefixed (domain : Set Config) marks count hPrefixed
                (domain.card - count)
            have hCountEq : count + (domain.card - count) = domain.card := Nat.add_sub_of_le hCount
            have hFinalEqual : tableIter (domain : Set Config) marks domain.card =
                    tableIter (domain : Set Config) marks count := by
                simpa only [hCountEq] using hEqual
            rw [hFinalEqual]
            exact hPrefixed
        have hCardLower : ∀ count, count ≤ domain.card →
                count ≤ (tableIter (domain : Set Config) marks count).ncard := by
            intro count hCount
            induction count with
            | zero => exact Nat.zero_le _
            | succ count ih =>
                    have hCountLe : count ≤ domain.card := Nat.le_trans (Nat.le_succ count) hCount
                    have hStrict := tableIter_ssubset_succ_of_not_prefixed (domain : Set Config) marks count
                        (hNoPrefixed count hCountLe)
                    have hFinite : (tableIter (domain : Set Config) marks (count + 1)).Finite :=
                        domain.finite_toSet.subset
                            (tableIter_subset_domain (domain : Set Config) marks (count + 1))
                    have hGrow := Set.ncard_lt_ncard hStrict hFinite
                    exact Nat.succ_le_iff.mpr ((ih hCountLe).trans_lt hGrow)
        have hStrict := tableIter_ssubset_succ_of_not_prefixed (domain : Set Config) marks domain.card
            (hNoPrefixed domain.card (Nat.le_refl _))
        have hFinite : (tableIter (domain : Set Config) marks (domain.card + 1)).Finite :=
            domain.finite_toSet.subset
                (tableIter_subset_domain (domain : Set Config) marks (domain.card + 1))
        have hGrow := Set.ncard_lt_ncard hStrict hFinite
        have hBound := Set.ncard_le_ncard
            (tableIter_subset_domain (domain : Set Config) marks (domain.card + 1))
            domain.finite_toSet
        have hLower := hCardLower domain.card (Nat.le_refl _)
        have hDomainCard : (domain : Set Config).ncard = domain.card := by simp
        omega

/-- Once the finite-cardinality bound is reached, every later round is pre-fixed too. -/
theorem tableIter_prefixed_of_card_le
                {Config : Type u}
                (domain : Finset Config)
                (marks : Set Config → Config → Prop)
                (count : Nat)
                (hCount : domain.card ≤ count) :
                tableStep (domain : Set Config) marks
                    (tableIter (domain : Set Config) marks count) ⊆
                        tableIter (domain : Set Config) marks count := by
        have hBase := tableIter_prefixed_at_card domain marks
        have hEqual := tableIter_add_eq_of_prefixed (domain : Set Config) marks domain.card hBase
            (count - domain.card)
        have hCountEq : domain.card + (count - domain.card) = count := Nat.add_sub_of_le hCount
        have hFinalEqual : tableIter (domain : Set Config) marks count =
                tableIter (domain : Set Config) marks domain.card := by
            rw [← hCountEq]
            exact hEqual
        rw [hFinalEqual]
        exact hBase

/-- Executable saturation rounds denote the corresponding proof-facing table iteration. -/
theorem saturateN_toFinset
        {Config : Type u} [DecidableEq Config]
        (configs : List Config)
        (contains : Config → List Config → Bool)
        (marks : List Config → Config → Bool)
        (marksSet : Set Config → Config → Prop)
        (hContains : ∀ config marked, contains config marked = true ↔ config ∈ marked)
        (hMarks : ∀ marked config,
            marks marked config = true ↔ marksSet (marked.toFinset : Set Config) config)
        (count : Nat) :
        ((saturateN configs contains marks count).toFinset : Set Config) =
            tableIter (configs.toFinset : Set Config) marksSet count := by
    induction count with
    | zero => simp [saturateN, tableIter]
    | succ count ih =>
        simpa [saturateN, tableIter, ih] using
            (saturateStep_toFinset configs (saturateN configs contains marks count)
                contains marks marksSet hContains hMarks)

/-- Every finite table approximation is contained in Mathlib's least fixed point. -/
theorem tableIter_subset_tableLfp
        {Config : Type u}
        (domain : Set Config)
        (marks : Set Config → Config → Prop)
        (hMarksMono : ∀ {left right}, left ⊆ right → ∀ config,
            marks left config → marks right config)
        (count : Nat) :
        tableIter domain marks count ⊆ tableLfp domain marks hMarksMono := by
    induction count with
    | zero => simp [tableIter]
    | succ count ih =>
        change tableStep domain marks (tableIter domain marks count) ⊆
            tableLfp domain marks hMarksMono
        rw [← tableStep_tableLfp domain marks hMarksMono]
        exact (tableStepHom domain marks hMarksMono).monotone ih

/-- A pre-fixed finite approximation is exactly Mathlib's least marker table. -/
theorem saturateN_eq_tableLfp_of_prefixed
        {Config : Type u} [DecidableEq Config]
        (configs : List Config)
        (contains : Config → List Config → Bool)
        (marks : List Config → Config → Bool)
        (marksSet : Set Config → Config → Prop)
        (hContains : ∀ config marked, contains config marked = true ↔ config ∈ marked)
        (hMarks : ∀ marked config,
            marks marked config = true ↔ marksSet (marked.toFinset : Set Config) config)
        (hMarksMono : ∀ {left right}, left ⊆ right → ∀ config,
            marksSet left config → marksSet right config)
        (count : Nat)
        (hPrefixed : tableStep (configs.toFinset : Set Config) marksSet
            (tableIter (configs.toFinset : Set Config) marksSet count) ⊆
              tableIter (configs.toFinset : Set Config) marksSet count) :
        ((saturateN configs contains marks count).toFinset : Set Config) =
            tableLfp (configs.toFinset : Set Config) marksSet hMarksMono := by
    rw [saturateN_toFinset configs contains marks marksSet hContains hMarks]
    apply Set.Subset.antisymm
    · exact tableIter_subset_tableLfp _ _ hMarksMono count
    · exact tableLfp_subset_of_prefixed _ _ hMarksMono _ hPrefixed

/-- Bounded executable saturation computes the Mathlib least marker table. -/
theorem saturate_toFinset_eq_tableLfp
        {Config : Type u} [DecidableEq Config]
        (configs : List Config)
        (contains : Config → List Config → Bool)
        (marks : List Config → Config → Bool)
        (marksSet : Set Config → Config → Prop)
        (hContains : ∀ config marked, contains config marked = true ↔ config ∈ marked)
        (hMarks : ∀ marked config,
            marks marked config = true ↔ marksSet (marked.toFinset : Set Config) config)
        (hMarksMono : ∀ {left right}, left ⊆ right → ∀ config,
            marksSet left config → marksSet right config) :
        ((saturate configs contains marks).toFinset : Set Config) =
            tableLfp (configs.toFinset : Set Config) marksSet hMarksMono := by
    unfold saturate
    exact saturateN_eq_tableLfp_of_prefixed configs contains marks marksSet hContains hMarks
      hMarksMono configs.length (by
                exact tableIter_prefixed_of_card_le configs.toFinset marksSet configs.length
                    configs.toFinset_card_le)

/-- Every Finset produced by the ordered powerset enumerator lies in its source list. -/
theorem powerset_member_subset (elements : List Element) (subset : FSet Element)
    (hSubset : subset ∈ powerset elements) :
    subset ⊆ elements.toFinset := by
  induction elements generalizing subset with
  | nil =>
      simp [powerset] at hSubset
      subst subset
      simp
  | cons head tail ih =>
      change subset ∈ powerset tail ++ (powerset tail).map (fun set => insert head set) at hSubset
      rw [List.mem_append] at hSubset
      rcases hSubset with hSubset | hSubset
      · exact fun element hElement => by
          simp only [List.toFinset_cons, Finset.mem_insert]
          exact Or.inr (ih subset hSubset hElement)
      · rw [List.mem_map] at hSubset
        rcases hSubset with ⟨candidate, hCandidate, rfl⟩
        intro element hElement
        simp only [List.toFinset_cons, Finset.mem_insert] at hElement ⊢
        rcases hElement with rfl | hElement
        · exact Or.inl rfl
        · exact Or.inr (ih candidate hCandidate hElement)

/-- The ordered powerset enumerator contains every subset of its source list. -/
theorem subset_mem_powerset (elements : List Element) (subset : FSet Element)
        (hSubset : subset ⊆ elements.toFinset) :
        subset ∈ powerset elements := by
    induction elements generalizing subset with
    | nil =>
        simpa [powerset] using hSubset
    | cons head tail ih =>
        by_cases hHead : head ∈ subset
        case pos =>
            have hSubsetTail : subset.erase head ⊆ tail.toFinset := by
                intro element hElement
                simp only [Finset.mem_erase] at hElement
                exact (Finset.mem_insert.mp (by simpa only [List.toFinset_cons] using hSubset hElement.2)).resolve_left hElement.1
            change subset ∈ powerset tail ++ (powerset tail).map (fun set => insert head set)
            grind
        case neg =>
            have hCandidate : subset.erase head ⊆ tail.toFinset :=
                fun element hElement =>
                    (Finset.mem_insert.mp (by simpa only [List.toFinset_cons] using hSubset (Finset.mem_erase.mp hElement).2)).resolve_left (Finset.mem_erase.mp hElement).1
            change subset ∈ powerset tail ++ (powerset tail).map (fun set => insert head set)
            grind

end EqCheckingAbstractInterpretation.FiniteEvaluator
