import EqCheckingAbstractInterpretation.Trace.Basic

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS

universe u v w

variable {Action : Type u} {Name : Type v} {Obs : Type w}

--/ ============================================================================
--/ 1. ABSTRACT TYPES FOR READY SIMULATION
--/ ============================================================================

abbrev ProcSet (Action : Type u) (Name : Type v) :=
  CCS Action Name → Prop

instance : Singleton (CCS Action Name) (ProcSet Action Name) where
  singleton q := fun r => r = q

instance : EmptyCollection (ProcSet Action Name) where
  emptyCollection := fun _ => False

abbrev ObsSet (Obs : Type w) := Obs → Prop

abbrev DiffSysRS (Action : Type u) (Name : Type v) (Obs : Type w) :=
  CCS Action Name → ProcSet Action Name → ObsSet Obs

--/ ============================================================================
--/ 2. CAPABILITY LATTICE FRAMEWORK
--/ ============================================================================

/-- Capability lattice elements from the paper: T, S, F, RS. -/
inductive Capability where
  | T
  | S
  | F
  | RS
  deriving DecidableEq, Repr

abbrev AbsSysRS (Action : Type u) (Name : Type v) :=
  CCS Action Name → ProcSet Action Name → Capability → Prop

/-- Order relation from the diamond lattice of capabilities. -/
def capLe : Capability → Capability → Prop
  | .T, _ => True
  | .S, .S => True
  | .S, .RS => True
  | .F, .F => True
  | .F, .RS => True
  | .RS, .RS => True
  | _, _ => False

instance : DecidableRel capLe := by
  intro c d
  cases c <;> cases d <;> simp [capLe]
  all_goals infer_instance

theorem capLe_refl (c : Capability) : capLe c c := by
  cases c <;> simp [capLe]

theorem capLe_trans {c d e : Capability}
    (hcd : capLe c d) (hde : capLe d e) : capLe c e := by
  cases c <;> cases d <;> cases e <;> simp [capLe] at hcd hde ⊢

/-- Join operation of the capability lattice. -/
def capJoin : Capability → Capability → Capability
  | .T, c => c
  | c, .T => c
  | .S, .S => .S
  | .F, .F => .F
  | _, _ => .RS

theorem capJoin_le
    {a b c : Capability}
    (h : capLe (capJoin a b) c) :
    capLe a c ∧ capLe b c := by
  cases a <;> cases b <;> cases c <;> simp [capJoin, capLe] at h ⊢

theorem capLe_left_capJoin
    (a b : Capability) :
    capLe a (capJoin a b) := by
  cases a <;> cases b <;> simp [capJoin, capLe]

theorem capLe_right_capJoin
    (a b : Capability) :
    capLe b (capJoin a b) := by
  cases a <;> cases b <;> simp [capJoin, capLe]

theorem capJoin_mono
    {a a' b b' : Capability}
    (ha : capLe a a')
    (hb : capLe b b') :
    capLe (capJoin a b) (capJoin a' b') := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    simp [capJoin, capLe] at ha hb ⊢

--/ ============================================================================
--/ 3. CAPABILITY ABSTRACTION INFRASTRUCTURE
--/ ============================================================================

/-- Capability requirement contributed by observation shape information. -/
def req (needsSim : Bool) (needsFail : Bool) : Capability :=
  if needsSim then
    if needsFail then .RS else .S
  else
    if needsFail then .F else .T

/-- Upward closure in the capability lattice. -/
def upClosure (X : Capability → Prop) : Capability → Prop :=
  fun d => ∃ c, X c ∧ capLe c d

/-- Capability abstraction without minimization/pruning. -/
def alphaCapRaw (ObsCap : Capability → Obs → Prop) (X : ObsSet Obs) : Capability → Prop :=
  fun c => ∃ o, X o ∧ ObsCap c o

/-- Minimal-capability pruning on capability predicates. -/
def minimalCap (A : Capability → Prop) (c : Capability) : Prop :=
  A c ∧ ∀ d, A d → capLe d c → capLe c d

/-- Capability abstraction with pruning to minimal capabilities. -/
def alphaCap (ObsCap : Capability → Obs → Prop) (X : ObsSet Obs) : Capability → Prop :=
  fun c => minimalCap (alphaCapRaw ObsCap X) c

/-- Concretization by upward closure of capabilities. -/
def gammaCap (ObsCap : Capability → Obs → Prop) (Y : Capability → Prop) : ObsSet Obs :=
  fun o => ∃ c, upClosure Y c ∧ ObsCap c o

/-- Threshold reading for an abstract capability value. -/
def thresholdWitness (A : Capability → Prop) (N : Capability) : Prop :=
  ∃ c, A c ∧ capLe c N

theorem thresholdWitness_iff_upClosure
    (A : Capability → Prop)
    (N : Capability) :
    thresholdWitness A N ↔ upClosure A N :=
  Iff.rfl

/-- Concrete threshold failure criterion for a difference relation. -/
def notPreorderAt
    (ObsCap : Capability → Obs → Prop)
    (Diff : DiffSysRS Action Name Obs)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) : Prop :=
  ∃ o, Diff p Q o ∧ ObsCap N o

/-- Abstract threshold failure criterion for a capability-valued analysis result. -/
def abstractFailsAt
    (Abs : AbsSysRS Action Name)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) : Prop :=
  thresholdWitness (Abs p Q) N

/--
Monotonicity condition needed for threshold soundness/completeness:
if a capability can observe `o`, then every stronger capability can observe `o`.
-/
def ObsCapMonotone (ObsCap : Capability → Obs → Prop) : Prop :=
  ∀ {c d o}, capLe c d → ObsCap c o → ObsCap d o

/--
Threshold reading for `alphaCapRaw`: it is equivalent to concrete intersection
with the threshold fragment, under monotonicity of fragment observability.
-/
theorem thresholdWitness_alphaCapRaw_iff
    (ObsCap : Capability → Obs → Prop)
    (hMono : ObsCapMonotone ObsCap)
    (X : ObsSet Obs)
    (N : Capability) :
    thresholdWitness (alphaCapRaw ObsCap X) N ↔
      ∃ o, X o ∧ ObsCap N o := by
  constructor
  · intro h
    rcases h with ⟨c, ⟨o, hX, hObs⟩, hLe⟩
    exact ⟨o, hX, hMono hLe hObs⟩
  · intro h
    rcases h with ⟨o, hX, hObs⟩
    exact ⟨N, ⟨o, hX, hObs⟩, capLe_refl N⟩

theorem minimalCap_left
    (A : Capability → Prop)
    {c : Capability}
    (h : minimalCap A c) : A c :=
  h.1

theorem thresholdWitness_minimalCap_of_mem
    (A : Capability → Prop)
    (N : Capability)
    (hAN : A N) :
    thresholdWitness (minimalCap A) N := by
  classical
  cases N with
  | T =>
      refine ⟨.T, ⟨hAN, ?_⟩, capLe_refl .T⟩
      intro d hAd hdT
      cases d <;> cases hdT <;> simp [capLe]
  | S =>
      by_cases hAT : A .T
      · refine ⟨.T, ⟨hAT, ?_⟩, by simp [capLe]⟩
        intro d hAd hdT
        cases d <;> cases hdT <;> simp [capLe]
      · refine ⟨.S, ⟨hAN, ?_⟩, capLe_refl .S⟩
        intro d hAd hdS
        cases d with
        | T => exact False.elim (hAT hAd)
        | S => exact capLe_refl .S
        | F => cases hdS
        | RS => cases hdS
  | F =>
      by_cases hAT : A .T
      · refine ⟨.T, ⟨hAT, ?_⟩, by simp [capLe]⟩
        intro d hAd hdT
        cases d <;> cases hdT <;> simp [capLe]
      · refine ⟨.F, ⟨hAN, ?_⟩, capLe_refl .F⟩
        intro d hAd hdF
        cases d with
        | T => exact False.elim (hAT hAd)
        | S => cases hdF
        | F => exact capLe_refl .F
        | RS => cases hdF
  | RS =>
      by_cases hAT : A .T
      · refine ⟨.T, ⟨hAT, ?_⟩, by simp [capLe]⟩
        intro d hAd hdT
        cases d <;> cases hdT <;> simp [capLe]
      · by_cases hAS : A .S
        · refine ⟨.S, ⟨hAS, ?_⟩, by simp [capLe]⟩
          intro d hAd hdS
          cases d with
          | T => exact False.elim (hAT hAd)
          | S => exact capLe_refl .S
          | F => cases hdS
          | RS => cases hdS
        · by_cases hAF : A .F
          · refine ⟨.F, ⟨hAF, ?_⟩, by simp [capLe]⟩
            intro d hAd hdF
            cases d with
            | T => exact False.elim (hAT hAd)
            | S => cases hdF
            | F => exact capLe_refl .F
            | RS => cases hdF
          · refine ⟨.RS, ⟨hAN, ?_⟩, capLe_refl .RS⟩
            intro d hAd hdRS
            cases d with
            | T => exact False.elim (hAT hAd)
            | S => exact False.elim (hAS hAd)
            | F => exact False.elim (hAF hAd)
            | RS => exact capLe_refl .RS

theorem upClosure_minimalCap_iff
    (A : Capability → Prop)
    (N : Capability) :
    upClosure (minimalCap A) N ↔ upClosure A N := by
  constructor
  · intro h
    rcases h with ⟨c, hc, hLe⟩
    exact ⟨c, minimalCap_left _ hc, hLe⟩
  · intro h
    rcases h with ⟨c, hAc, hLe⟩
    rcases thresholdWitness_minimalCap_of_mem A c hAc with ⟨d, hd, hdLe⟩
    exact ⟨d, hd, capLe_trans hdLe hLe⟩

theorem alphaCapRaw_upward_closed
    (ObsCap : Capability → Obs → Prop)
    (hMono : ObsCapMonotone ObsCap)
    (X : ObsSet Obs)
    (N : Capability) :
    upClosure (alphaCapRaw ObsCap X) N ↔ alphaCapRaw ObsCap X N := by
  constructor
  · intro h
    rcases h with ⟨c, ⟨o, hX, hObs⟩, hLe⟩
    exact ⟨o, hX, hMono hLe hObs⟩
  · intro h
    exact ⟨N, h, capLe_refl N⟩

theorem upClosure_alphaCap_iff_alphaCapRaw
    (ObsCap : Capability → Obs → Prop)
    (hMono : ObsCapMonotone ObsCap)
    (X : ObsSet Obs)
    (N : Capability) :
    upClosure (alphaCap ObsCap X) N ↔ alphaCapRaw ObsCap X N := by
  unfold alphaCap
  rw [upClosure_minimalCap_iff]
  exact alphaCapRaw_upward_closed ObsCap hMono X N

/-- Threshold reading for `alphaCap`: pruning preserves threshold information. -/
theorem thresholdWitness_alphaCap_iff
    (ObsCap : Capability → Obs → Prop)
    (hMono : ObsCapMonotone ObsCap)
    (X : ObsSet Obs)
    (N : Capability) :
    thresholdWitness (alphaCap ObsCap X) N ↔
      ∃ o, X o ∧ ObsCap N o := by
  constructor
  · intro h
    rcases h with ⟨c, hc, hLe⟩
    exact (thresholdWitness_alphaCapRaw_iff ObsCap hMono X N).1
      ⟨c, minimalCap_left _ hc, hLe⟩
  · intro h
    rcases h with ⟨o, hX, hObsN⟩
    simpa [alphaCap] using thresholdWitness_minimalCap_of_mem
      (alphaCapRaw ObsCap X)
      N
      ⟨o, hX, hObsN⟩

/--
Unified threshold theorem at the level used in Section 5:
if abstract values are pointwise `alphaCapRaw` of concrete differences,
then abstract threshold witnesses are exactly concrete threshold failures.
-/
theorem abstractFailsAt_iff_notPreorderAt_of_alpha
    (ObsCap : Capability → Obs → Prop)
    (hMono : ObsCapMonotone ObsCap)
    (Diff : DiffSysRS Action Name Obs)
    (Abs : AbsSysRS Action Name)
    (hAlpha : ∀ p Q c, Abs p Q c ↔ alphaCapRaw ObsCap (Diff p Q) c)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt Abs N p Q ↔ notPreorderAt ObsCap Diff N p Q := by
  change thresholdWitness (Abs p Q) N ↔ _
  have hEq : (Abs p Q) = alphaCapRaw ObsCap (Diff p Q) := by
    funext c
    apply propext
    exact hAlpha p Q c
  rw [hEq]
  exact thresholdWitness_alphaCapRaw_iff ObsCap hMono (Diff p Q) N

/-- Exact-pruned variant of the unified threshold theorem. -/
theorem abstractFailsAt_iff_notPreorderAt_of_alphaExact
    (ObsCap : Capability → Obs → Prop)
    (hMono : ObsCapMonotone ObsCap)
    (Diff : DiffSysRS Action Name Obs)
    (Abs : AbsSysRS Action Name)
    (hAlpha : ∀ p Q c, Abs p Q c ↔ alphaCap ObsCap (Diff p Q) c)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt Abs N p Q ↔ notPreorderAt ObsCap Diff N p Q := by
  change thresholdWitness (Abs p Q) N ↔ _
  have hEq : (Abs p Q) = alphaCap ObsCap (Diff p Q) := by
    funext c
    apply propext
    exact hAlpha p Q c
  rw [hEq]
  exact thresholdWitness_alphaCap_iff ObsCap hMono (Diff p Q) N

/--
Least-fixpoint variant matching the paper's Section 5 statement shape.
`lfpAbs` is the abstract lfp result, `lfpConcrete` the concrete one.
-/
theorem abstractFailsAt_iff_notPreorderAt_of_lfp
    (ObsCap : Capability → Obs → Prop)
    (hMono : ObsCapMonotone ObsCap)
    (lfpConcrete : DiffSysRS Action Name Obs)
    (lfpAbs : AbsSysRS Action Name)
    (hLfp : ∀ p Q c, lfpAbs p Q c ↔ alphaCapRaw ObsCap (lfpConcrete p Q) c)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt lfpAbs N p Q ↔ notPreorderAt ObsCap lfpConcrete N p Q := by
  exact abstractFailsAt_iff_notPreorderAt_of_alpha
    (ObsCap := ObsCap)
    hMono
    lfpConcrete
    lfpAbs
    hLfp
    N p Q

/-- Least-fixpoint threshold theorem for exact-pruned capability values. -/
theorem abstractFailsAt_iff_notPreorderAt_of_lfpExact
    (ObsCap : Capability → Obs → Prop)
    (hMono : ObsCapMonotone ObsCap)
    (lfpConcrete : DiffSysRS Action Name Obs)
    (lfpAbs : AbsSysRS Action Name)
    (hLfp : ∀ p Q c, lfpAbs p Q c ↔ alphaCap ObsCap (lfpConcrete p Q) c)
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    abstractFailsAt lfpAbs N p Q ↔ notPreorderAt ObsCap lfpConcrete N p Q := by
  exact abstractFailsAt_iff_notPreorderAt_of_alphaExact
    (ObsCap := ObsCap)
    hMono
    lfpConcrete
    lfpAbs
    hLfp
    N p Q

--/ ============================================================================
--/ 4. READY SIMULATION OBSERVATIONS (RSObs)
--/ ============================================================================

/--
Concrete observation syntax used to instantiate the unified capability framework:
positive branching plus negative (refusal) tests.
-/
inductive RSObs (Action : Type u) where
  | tt
  | node : List (Action × RSObs Action) → List Action → RSObs Action
  deriving Repr

mutual

/-- Aggregate child capability requirements from positive branches. -/
def childrenReq : List (Action × RSObs Action) → Capability
  | [] => .T
  | (_, o) :: xs => capJoin (reqOfObs o) (childrenReq xs)

/-- Least capability needed to express a concrete ready-simulation observation. -/
def reqOfObs : RSObs Action → Capability
  | .tt => .T
  | .node pos neg =>
      let selfReq : Capability := req (decide (1 < pos.length)) (!neg.isEmpty)
      capJoin selfReq (childrenReq pos)

end

/-- Fragment membership predicate induced by capability thresholds. -/
def rsObsCap (c : Capability) (o : RSObs Action) : Prop :=
  capLe (reqOfObs o) c

/-- Observation fragments corresponding to Tr/S/F/RS thresholds. -/
def ObsTr : RSObs Action → Prop := rsObsCap .T

def ObsS : RSObs Action → Prop := rsObsCap .S

def ObsF : RSObs Action → Prop := rsObsCap .F

def ObsRS : RSObs Action → Prop := rsObsCap .RS

theorem childrenReq_member_le
    {ao : Action × RSObs Action}
    {pos : List (Action × RSObs Action)}
    (hMem : ao ∈ pos) :
    capLe (reqOfObs ao.2) (childrenReq pos) := by
  induction pos with
  | nil => cases hMem
  | cons head tl ih =>
      simp only [childrenReq]
      simp only [List.mem_cons] at hMem
      rcases hMem with rfl | hMem
      · exact capLe_left_capJoin (reqOfObs ao.2) (childrenReq tl)
      · exact capLe_trans (ih hMem) (capLe_right_capJoin (reqOfObs head.2) (childrenReq tl))

theorem childrenReq_map_le
    (f : Action × RSObs Action → RSObs Action)
    (pos : List (Action × RSObs Action))
    (hLe : ∀ ao, ao ∈ pos → capLe (reqOfObs (f ao)) (reqOfObs ao.2)) :
    capLe (childrenReq (pos.map (fun ao => (ao.1, f ao)))) (childrenReq pos) := by
  induction pos with
  | nil => exact capLe_refl _
  | cons head tl ih =>
      simp only [List.map, childrenReq]
      refine capJoin_mono ?_ ?_
      · exact hLe head (by simp)
      · refine ih ?_
        intro ao hao
        exact hLe ao (by simp [hao])

theorem reqOfObs_node_map_le
    (f : Action × RSObs Action → RSObs Action)
    (pos : List (Action × RSObs Action))
    (neg : List Action)
    (hLe : ∀ ao, ao ∈ pos → capLe (reqOfObs (f ao)) (reqOfObs ao.2)) :
    capLe (reqOfObs (.node (pos.map (fun ao => (ao.1, f ao))) neg))
      (reqOfObs (.node pos neg)) := by
  simp [reqOfObs, List.length_map]
  exact capJoin_mono (capLe_refl _) (childrenReq_map_le f pos hLe)

/-- Replace children by branch occurrence rather than branch value. -/
def replaceChildren
    (pos : List (Action × RSObs Action))
    (f : Fin pos.length → RSObs Action) :
    List (Action × RSObs Action) :=
  match pos with
  | [] => []
  | (a, _) :: xs =>
      (a, f ⟨0, by simp⟩) ::
        replaceChildren xs (fun i => f ⟨i.1 + 1, by simp [Nat.succ_lt_succ i.2]⟩)

theorem replaceChildren_length
    (pos : List (Action × RSObs Action))
    (f : Fin pos.length → RSObs Action) :
    (replaceChildren pos f).length = pos.length := by
  induction pos with
  | nil => simp [replaceChildren]
  | cons head tl ih =>
      simp [replaceChildren, ih]

theorem replaceChildren_get
    (pos : List (Action × RSObs Action))
    (f : Fin pos.length → RSObs Action)
    (i : Fin pos.length) :
    (replaceChildren pos f).get ⟨i.1, by simp [replaceChildren_length, i.2]⟩ =
      ((pos.get i).1, f i) := by
  induction pos with
  | nil => cases i.2
  | cons head tl ih =>
      rcases i with ⟨n, hn⟩
      cases n with
      | zero =>
          simp [replaceChildren]
      | succ n =>
          simpa [replaceChildren] using
            (ih (fun i => f ⟨i.1 + 1, by simp⟩)
              ⟨n, by simpa using hn⟩)

theorem childrenReq_replaceChildren_le
    (pos : List (Action × RSObs Action))
    (f : Fin pos.length → RSObs Action)
    (hLe : ∀ i, capLe (reqOfObs (f i)) (reqOfObs (pos.get i).2)) :
    capLe (childrenReq (replaceChildren pos f)) (childrenReq pos) := by
  induction pos with
  | nil => exact capLe_refl _
  | cons head tl ih =>
      simp [replaceChildren, childrenReq]
      refine capJoin_mono ?_ ?_
      · simpa using hLe ⟨0, by simp⟩
      · refine ih (fun i => f ⟨i.1 + 1, by simp⟩) ?_
        intro i
        simpa using hLe ⟨i.1 + 1, by simp⟩

theorem reqOfObs_node_replaceChildren_le
    (pos : List (Action × RSObs Action))
    (neg : List Action)
    (f : Fin pos.length → RSObs Action)
    (hLe : ∀ i, capLe (reqOfObs (f i)) (reqOfObs (pos.get i).2)) :
    capLe (reqOfObs (.node (replaceChildren pos f) neg)) (reqOfObs (.node pos neg)) := by
  simp [reqOfObs, replaceChildren_length]
  exact capJoin_mono (capLe_refl _) (childrenReq_replaceChildren_le pos f hLe)

theorem rsObsCap_child
    {N : Capability}
    {pos : List (Action × RSObs Action)}
    {neg : List Action}
    {ao : Action × RSObs Action}
    (hCap : rsObsCap N (.node pos neg))
    (hMem : ao ∈ pos) :
    rsObsCap N ao.2 := by
  unfold rsObsCap at hCap ⊢
  dsimp [reqOfObs] at hCap
  exact capLe_trans (childrenReq_member_le hMem) ((capJoin_le hCap).2)

theorem rsObsCap_S_node_neg_nil
    {pos : List (Action × RSObs Action)}
    {neg : List Action}
    (hCap : rsObsCap .S (.node pos neg)) :
    neg = [] := by
  unfold rsObsCap at hCap
  dsimp [reqOfObs] at hCap
  have hSelf : capLe (req (decide (1 < pos.length)) (!neg.isEmpty)) .S := (capJoin_le hCap).1
  cases neg with
  | nil => rfl
  | cons b bs =>
      by_cases hLen : 1 < pos.length
      · simp [req, hLen, capLe] at hSelf
      · simp [req, hLen, capLe] at hSelf

theorem rsObsCap_T_node_neg_nil
    {pos : List (Action × RSObs Action)}
    {neg : List Action}
    (hCap : rsObsCap .T (.node pos neg)) :
    neg = [] := by
  unfold rsObsCap at hCap
  dsimp [reqOfObs] at hCap
  have hSelf : capLe (req (decide (1 < pos.length)) (!neg.isEmpty)) .T := (capJoin_le hCap).1
  cases neg with
  | nil => rfl
  | cons b bs =>
      by_cases hLen : 1 < pos.length
      · simp [req, hLen, capLe] at hSelf
      · simp [req, hLen, capLe] at hSelf

theorem rsObsCap_F_node_no_branching
    {pos : List (Action × RSObs Action)}
    {neg : List Action}
    (hCap : rsObsCap .F (.node pos neg)) :
    ¬ 1 < pos.length := by
  unfold rsObsCap at hCap
  dsimp [reqOfObs] at hCap
  have hSelf : capLe (req (decide (1 < pos.length)) (!neg.isEmpty)) .F := (capJoin_le hCap).1
  by_cases hLen : 1 < pos.length
  · simp [req, hLen, capLe] at hSelf
    by_cases hNil : neg = []
    · simp [hNil] at hSelf
    · simp [hNil] at hSelf
  · exact hLen

theorem rsObsCap_T_node_no_branching
    {pos : List (Action × RSObs Action)}
    {neg : List Action}
    (hCap : rsObsCap .T (.node pos neg)) :
    ¬ 1 < pos.length := by
  unfold rsObsCap at hCap
  dsimp [reqOfObs] at hCap
  have hSelf : capLe (req (decide (1 < pos.length)) (!neg.isEmpty)) .T := (capJoin_le hCap).1
  by_cases hLen : 1 < pos.length
  · simp [req, hLen, capLe] at hSelf
    by_cases hNil : neg = []
    · simp [hNil] at hSelf
    · simp [hNil] at hSelf
  · exact hLen

theorem rsObsCapMonotone : ObsCapMonotone (Obs := RSObs Action) rsObsCap := by
  intro c d o hcd hObs
  exact capLe_trans hObs hcd

/-- Threshold reading as concrete fragment intersection for this instance. -/
theorem notPreorderAt_iff_intersects_fragment
    (Diff : DiffSysRS Action Name (RSObs Action))
    (N : Capability)
    (p : CCS Action Name)
    (Q : ProcSet Action Name) :
    notPreorderAt rsObsCap Diff N p Q ↔ ∃ o, Diff p Q o ∧ rsObsCap N o := by
  rfl

end EqCheckingAbstractInterpretation.Ready
