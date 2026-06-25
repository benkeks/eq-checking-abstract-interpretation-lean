import EqCheckingAbstractInterpretation.Ready.Correctness

namespace EqCheckingAbstractInterpretation.Ready.RunningExample

open EqCheckingAbstractInterpretation.CCS
open EqCheckingAbstractInterpretation.Ready
open EqCheckingAbstractInterpretation.Trace

/-!
## Running Example: Abstract RS Differences

We use the following processes from the trace running example:

  `PA   = a.PA + a.b.0`
  `PB   = a.(PB + b.0)`
  `b0   = b.0`               (only enables b)
  `PBb0 = PB + b.0`          (enables both a and b)

Key RS results:

1. `abstractRSDiffExact_PA_PB_at_F`:
  F-capability witnesses `PA ≰_F PB` via the concrete observation
  `⟨a⟩¬b`: after one `a`-step, choose the looping `PA` branch, which refuses `b`,
  while `PB` moves to `PBb0`, which enables `b`.

2. `abstractRSDiffExact_PB_PA_at_S`:
  S-capability witnesses `PB ≰_S PA` via the simulation observation
  `⟨a⟩(⟨a⟩⊤ ∧ ⟨b⟩⊤)`: after one `a`-step, `PB` reaches `PBb0`, which can do both
  `a` and `b`, while the two right-hand successors of `PA` split the failure:
  `b0` cannot do `a`, and `PA` cannot do `b`.
-/

-- ---------------------------------------------------------------------------
-- Action and name types
-- ---------------------------------------------------------------------------

-- For the example, we will use one-letter lower-case constructor names,
-- to align with the paper. This naturally triigers some warnings, which we surpress.
-- (But you don't want to import these names into wider formalizations...)
set_option linter.constructorNameAsVariable false

inductive RunAct where
  | a
  | b
  deriving DecidableEq, Repr

inductive RunName where
  | PA
  | PB
  deriving DecidableEq, Repr

abbrev RunProc := CCS RunAct RunName

def PA : RunProc := .var .PA
def PB : RunProc := .var .PB

/-- `PA ↦ a.PA + a.b.0`, `PB ↦ a.(PB + b.0)` -/
def runEnv : Env RunAct RunName
  | .PA => .choice (.prefix .a (.var .PA)) (.prefix .a (.prefix .b .zero))
  | .PB => .prefix .a (.choice (.var .PB) (.prefix .b .zero))

def b0   : RunProc := .prefix .b .zero
def PBb0 : RunProc := .choice (.var .PB) (.prefix .b .zero)

-- ---------------------------------------------------------------------------
-- Derivative facts
-- ---------------------------------------------------------------------------

/-- PBb0 can do action a, looping back to itself. -/
theorem PBb0_a_PBb0 : Deriv runEnv PBb0 .a PBb0 :=
  .choice_left (.var .prefix)

/-- PA can do action a, looping back to itself. -/
theorem PA_a_PA : Deriv runEnv PA .a PA :=
  .var (.choice_left .prefix)

/-- PA can do action a, reaching b0. -/
theorem PA_a_b0 : Deriv runEnv PA .a b0 :=
  .var (.choice_right .prefix)

/-- PB can do action a, reaching PBb0. -/
theorem PB_a_PBb0 : Deriv runEnv PB .a PBb0 :=
  .var .prefix

/-- PBb0 can do action b, reaching zero. -/
theorem PBb0_b_zero : Deriv runEnv PBb0 .b .zero :=
  .choice_right .prefix

/-- b0 = b.0 cannot do action a. -/
theorem b0_a_not_enabled : ¬ Enabled runEnv b0 .a := by
  intro ⟨_, h⟩; cases h

theorem PBb0_a_enabled : Enabled runEnv PBb0 .a :=
  ⟨PBb0, PBb0_a_PBb0⟩

theorem PBb0_b_enabled : Enabled runEnv PBb0 .b :=
  ⟨.zero, PBb0_b_zero⟩

theorem zero_no_deriv (a : RunAct) (p : RunProc) : ¬ Deriv runEnv (.zero : RunProc) a p := by
  intro h
  cases h

theorem b0_deriv_cases {a : RunAct} {p : RunProc} (h : Deriv runEnv b0 a p) :
    a = .b ∧ p = (.zero : RunProc) := by
  cases h
  constructor <;> rfl

theorem PA_deriv_cases {a : RunAct} {p : RunProc} (h : Deriv runEnv PA a p) :
    a = .a ∧ (p = PA ∨ p = b0) := by
  cases h with
  | var hInner =>
      cases hInner with
      | choice_left hPrefix =>
          cases hPrefix
          exact ⟨rfl, Or.inl rfl⟩
      | choice_right hPrefix =>
          cases hPrefix
          exact ⟨rfl, Or.inr rfl⟩

theorem PB_deriv_cases {a : RunAct} {p : RunProc} (h : Deriv runEnv PB a p) :
    a = .a ∧ p = PBb0 := by
  cases h with
  | var hInner =>
      cases hInner
      exact ⟨rfl, rfl⟩

theorem PBb0_deriv_cases {a : RunAct} {p : RunProc} (h : Deriv runEnv PBb0 a p) :
    (a = .a ∧ p = PBb0) ∨ (a = .b ∧ p = (.zero : RunProc)) := by
  cases h with
  | choice_left hLeft =>
      cases hLeft with
      | var hInner =>
          cases hInner
          exact Or.inl ⟨rfl, rfl⟩
  | choice_right hRight =>
      cases hRight
      exact Or.inr ⟨rfl, rfl⟩

theorem single_branch_tail_nil {α : Type} {x : α} {xs : List α}
    (h : ¬ 1 < (x :: xs).length) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons y ys =>
      exfalso
      exact h (by simp)

/-- PA cannot do action b. -/
theorem PA_b_not_enabled : ¬ Enabled runEnv PA .b := by
  intro ⟨_, h⟩
  cases h with
  | var h' =>
      cases h' with
      | choice_left h'' => cases h''
      | choice_right h'' => cases h''

-- ---------------------------------------------------------------------------
-- Observation: refuse a (no positive branches, neg = [a])
-- ---------------------------------------------------------------------------

/-- The RS observation `¬a` (refuse a, no positives). Capability: F. -/
def obs_neg_a : RSObs RunAct := .node [] [.a]

/-- The RS observation `¬b` (refuse b, no positives). Capability: F. -/
def obs_neg_b : RSObs RunAct := .node [] [.b]

/-- The failure witness `⟨a⟩¬b`. Capability: F. -/
def obs_a_neg_b : RSObs RunAct := .node [(.a, obs_neg_b)] []

/-- The simulation branching witness `⟨a⟩⊤ ∧ ⟨b⟩⊤`. Capability: S. -/
def obs_split_ab : RSObs RunAct := .node [(.a, .tt), (.b, .tt)] []

/-- The simulation witness `⟨a⟩(⟨a⟩⊤ ∧ ⟨b⟩⊤)`. Capability: S. -/
def obs_a_split_ab : RSObs RunAct := .node [(.a, obs_split_ab)] []

-- ---------------------------------------------------------------------------
-- Capability lemma
-- ---------------------------------------------------------------------------

theorem rsObsCap_F_obs_neg_a : rsObsCap .F obs_neg_a := by
  show capLe (reqOfObs obs_neg_a) .F
  change capLe .F .F
  exact capLe_refl .F

theorem rsObsCap_F_obs_a_neg_b : rsObsCap .F obs_a_neg_b := by
  show capLe (reqOfObs obs_a_neg_b) .F
  change capLe .F .F
  exact capLe_refl .F

theorem rsObsCap_S_obs_a_split_ab : rsObsCap .S obs_a_split_ab := by
  show capLe (reqOfObs obs_a_split_ab) .S
  change capLe .S .S
  exact capLe_refl .S

def noSRegion (p : RunProc) (Q : ProcSet RunAct RunName) : Prop :=
  (p = PA ∧ (Q PB ∨ Q PBb0)) ∨
  (p = b0 ∧ Q PBb0) ∨
  (p = (.zero : RunProc) ∧ Q (.zero : RunProc))

def rhoNoS : DiffSysRS RunAct RunName (RSObs RunAct) :=
  fun p Q o => noSRegion p Q → ¬ rsObsCap .S o

def noFRegion (p : RunProc) (Q : ProcSet RunAct RunName) : Prop :=
  (p = PB ∧ Q PA) ∨
  (p = PBb0 ∧ Q PA ∧ Q b0) ∨
  (p = (.zero : RunProc) ∧ Q (.zero : RunProc))

def rhoNoF : DiffSysRS RunAct RunName (RSObs RunAct) :=
  fun p Q o => noFRegion p Q → ¬ rsObsCap .F o

theorem rhoNoS_prefixpoint :
    ∀ p Q o, DRS runEnv rhoNoS p Q o → rhoNoS p Q o := by
  intro p Q o hDRS hRegion hCapS
  cases o with
  | tt =>
      rcases hRegion with hPA | hRest
      · rcases hPA with ⟨rfl, hQPB | hQPBb0⟩
        · exact hDRS PB hQPB
        · exact hDRS PBb0 hQPBb0
      · rcases hRest with hB0 | hZero
        · rcases hB0 with ⟨rfl, hQPBb0⟩
          exact hDRS PBb0 hQPBb0
        · rcases hZero with ⟨rfl, hQZero⟩
          exact hDRS (.zero : RunProc) hQZero
  | node pos neg =>
      rcases hDRS with ⟨Qneg, Qpos, hPos, hNegP, hNegQ, hCover⟩
      have hNegNil : neg = [] := rsObsCap_S_node_neg_nil hCapS
      have hQnegFalse : ∀ q, ¬ Qneg q := by
        intro q hq
        rcases hNegQ q hq with ⟨b, hb, _⟩
        simp [hNegNil] at hb
      have hChildCap : ∀ i : Fin pos.length, rsObsCap .S (pos.get i).2 := by
        intro i
        exact rsObsCap_child hCapS (by simp)
      rcases hRegion with hPA | hRest
      · rcases hPA with ⟨rfl, hQPB | hQPBb0⟩
        · rcases hCover PB hQPB with hPBneg | ⟨i, hQPB_i⟩
          · exact False.elim (hQnegFalse PB hPBneg)
          · rcases hPos i with ⟨p', hDer, hChild⟩
            have ha : (pos.get i).1 = .a := (PA_deriv_cases hDer).1
            have hQPBb0a : DerivSetOf runEnv (Qpos i) .a PBb0 := by
              refine ⟨PB, hQPB_i, ?_⟩
              exact PB_a_PBb0
            have hChildRegion : noSRegion p' (DerivSetOf runEnv (Qpos i) (pos.get i).1) := by
              rcases PA_deriv_cases hDer with ⟨ha, hCase⟩
              rcases hCase with rfl | rfl
              · have hQPBb0 : DerivSetOf runEnv (Qpos i) (pos.get i).1 PBb0 := by
                  rw [ha]
                  exact hQPBb0a
                exact Or.inl ⟨rfl, Or.inr hQPBb0⟩
              · have hQPBb0 : DerivSetOf runEnv (Qpos i) (pos.get i).1 PBb0 := by
                  rw [ha]
                  exact hQPBb0a
                exact Or.inr <| Or.inl ⟨rfl, hQPBb0⟩
            exact hChild hChildRegion (hChildCap i)
        · rcases hCover PBb0 hQPBb0 with hPBb0neg | ⟨i, hQPBb0_i⟩
          · exact False.elim (hQnegFalse PBb0 hPBb0neg)
          · rcases hPos i with ⟨p', hDer, hChild⟩
            have ha : (pos.get i).1 = .a := (PA_deriv_cases hDer).1
            have hQPBb0a : DerivSetOf runEnv (Qpos i) .a PBb0 := by
              refine ⟨PBb0, hQPBb0_i, ?_⟩
              exact PBb0_a_PBb0
            have hChildRegion : noSRegion p' (DerivSetOf runEnv (Qpos i) (pos.get i).1) := by
              rcases PA_deriv_cases hDer with ⟨ha, hCase⟩
              rcases hCase with rfl | rfl
              · have hQPBb0' : DerivSetOf runEnv (Qpos i) (pos.get i).1 PBb0 := by
                  rw [ha]
                  exact hQPBb0a
                exact Or.inl ⟨rfl, Or.inr hQPBb0'⟩
              · have hQPBb0' : DerivSetOf runEnv (Qpos i) (pos.get i).1 PBb0 := by
                  rw [ha]
                  exact hQPBb0a
                exact Or.inr <| Or.inl ⟨rfl, hQPBb0'⟩
            exact hChild hChildRegion (hChildCap i)
      · rcases hRest with hB0 | hZero
        · rcases hB0 with ⟨rfl, hQPBb0⟩
          rcases hCover PBb0 hQPBb0 with hPBb0neg | ⟨i, hQPBb0_i⟩
          · exact False.elim (hQnegFalse PBb0 hPBb0neg)
          · rcases hPos i with ⟨p', hDer, hChild⟩
            have hb : (pos.get i).1 = .b := (b0_deriv_cases hDer).1
            have hQZerob : DerivSetOf runEnv (Qpos i) .b (.zero : RunProc) := by
              refine ⟨PBb0, hQPBb0_i, ?_⟩
              exact PBb0_b_zero
            have hChildRegion : noSRegion p' (DerivSetOf runEnv (Qpos i) (pos.get i).1) := by
              rcases b0_deriv_cases hDer with ⟨hb, hp'⟩
              have hQZero : DerivSetOf runEnv (Qpos i) (pos.get i).1 (.zero : RunProc) := by
                rw [hb]
                exact hQZerob
              subst hp'
              exact Or.inr <| Or.inr ⟨rfl, hQZero⟩
            exact hChild hChildRegion (hChildCap i)
        · rcases hZero with ⟨rfl, hQZero⟩
          rcases hCover (.zero : RunProc) hQZero with hZneg | ⟨i, _⟩
          · exact False.elim (hQnegFalse (.zero : RunProc) hZneg)
          · rcases hPos i with ⟨p', hDer, _⟩
            exact zero_no_deriv _ _ hDer

theorem lfpDRS_noS_of_noSRegion
    {p : RunProc}
    {Q : ProcSet RunAct RunName}
    (hRegion : noSRegion p Q) :
    ∀ o, lfpDRS runEnv p Q o → ¬ rsObsCap .S o := by
  intro o hLfp
  exact hLfp rhoNoS rhoNoS_prefixpoint hRegion

theorem rhoNoF_prefixpoint :
    ∀ p Q o, DRS runEnv rhoNoF p Q o → rhoNoF p Q o := by
  intro p Q o hDRS hRegion hCapF
  cases o with
  | tt =>
      rcases hRegion with hPB | hRest
      · rcases hPB with ⟨rfl, hQPA⟩
        exact hDRS PA hQPA
      · rcases hRest with hPBb0 | hZero
        · rcases hPBb0 with ⟨rfl, hQPA, _⟩
          exact hDRS PA hQPA
        · rcases hZero with ⟨rfl, hQZero⟩
          exact hDRS (.zero : RunProc) hQZero
  | node pos neg =>
      rcases hDRS with ⟨Qneg, Qpos, hPos, hNegP, hNegQ, hCover⟩
      have hNoBranch : ¬ 1 < pos.length := rsObsCap_F_node_no_branching hCapF
      have hChildCap : ∀ i : Fin pos.length, rsObsCap .F (pos.get i).2 := by
        intro i
        exact rsObsCap_child hCapF (by simp)
      rcases hRegion with hPB | hRest
      · rcases hPB with ⟨rfl, hQPA⟩
        rcases hCover PA hQPA with hPAneg | ⟨i, hQPA_i⟩
        · rcases hNegQ PA hPAneg with ⟨b, hb, ⟨q, hDer⟩⟩
          rcases PA_deriv_cases hDer with ⟨hbAct, _⟩
          subst hbAct
          exact hNegP .a hb ⟨PBb0, PB_a_PBb0⟩
        · rcases hPos i with ⟨p', hDer, hChild⟩
          rcases PB_deriv_cases hDer with ⟨ha, hp'⟩
          have hQPAa : DerivSetOf runEnv (Qpos i) .a PA := by
            exact ⟨PA, hQPA_i, PA_a_PA⟩
          have hQb0a : DerivSetOf runEnv (Qpos i) .a b0 := by
            exact ⟨PA, hQPA_i, PA_a_b0⟩
          have hChildRegion : noFRegion p' (DerivSetOf runEnv (Qpos i) (pos.get i).1) := by
            rw [ha, hp']
            exact Or.inr <| Or.inl ⟨rfl, hQPAa, hQb0a⟩
          exact hChild hChildRegion (hChildCap i)
      · rcases hRest with hPBb0 | hZero
        · rcases hPBb0 with ⟨rfl, hQPA, hQb0⟩
          have hPAbranch : ∃ i, Qpos i PA := by
            rcases hCover PA hQPA with hPAneg | hBranch
            · rcases hNegQ PA hPAneg with ⟨b, hb, ⟨q, hDer⟩⟩
              rcases PA_deriv_cases hDer with ⟨hbAct, _⟩
              subst hbAct
              exact False.elim (hNegP .a hb PBb0_a_enabled)
            · exact hBranch
          have hBbranch : ∃ i, Qpos i b0 := by
            rcases hCover b0 hQb0 with hBneg | hBranch
            · rcases hNegQ b0 hBneg with ⟨b, hb, ⟨q, hDer⟩⟩
              rcases b0_deriv_cases hDer with ⟨hbAct, _⟩
              subst hbAct
              exact False.elim (hNegP .b hb PBb0_b_enabled)
            · exact hBranch
          cases pos with
          | nil =>
              rcases hPAbranch with ⟨i, _⟩
              exact False.elim (Fin.elim0 i)
          | cons head tl =>
              have htl : tl = [] := single_branch_tail_nil hNoBranch
              subst htl
              let i0 : Fin ([head].length) := ⟨0, by simp⟩
              have hQPA0 : Qpos i0 PA := by
                rcases hPAbranch with ⟨i, hi⟩
                rcases i with ⟨n, hn⟩
                cases n with
                | zero => simpa [i0] using hi
                | succ n => simp at hn
              have hQb00 : Qpos i0 b0 := by
                rcases hBbranch with ⟨i, hi⟩
                rcases i with ⟨n, hn⟩
                cases n with
                | zero => simpa [i0] using hi
                | succ n => simp at hn
              rcases hPos i0 with ⟨p', hDer, hChild⟩
              rcases PBb0_deriv_cases hDer with ⟨ha, hp'⟩ | ⟨hb, hp'⟩
              · have hQPAa : DerivSetOf runEnv (Qpos i0) .a PA := by
                  exact ⟨PA, hQPA0, PA_a_PA⟩
                have hQb0a : DerivSetOf runEnv (Qpos i0) .a b0 := by
                  exact ⟨PA, hQPA0, PA_a_b0⟩
                have hChildRegion : noFRegion p' (DerivSetOf runEnv (Qpos i0) .a) := by
                  rw [hp']
                  exact Or.inr <| Or.inl ⟨rfl, hQPAa, hQb0a⟩
                rw [ha] at hChild
                exact hChild hChildRegion (hChildCap i0)
              · have hQZerob : DerivSetOf runEnv (Qpos i0) .b (.zero : RunProc) := by
                  refine ⟨b0, hQb00, ?_⟩
                  simpa [b0] using (Deriv.prefix : Deriv runEnv (.prefix .b .zero) .b (.zero : RunProc))
                have hChildRegion : noFRegion p' (DerivSetOf runEnv (Qpos i0) .b) := by
                  rw [hp']
                  exact Or.inr <| Or.inr ⟨rfl, hQZerob⟩
                rw [hb] at hChild
                exact hChild hChildRegion (hChildCap i0)
        · rcases hZero with ⟨rfl, hQZero⟩
          rcases hCover (.zero : RunProc) hQZero with hZneg | ⟨i, _⟩
          · rcases hNegQ (.zero : RunProc) hZneg with ⟨b, hb, ⟨q, hDer⟩⟩
            exact zero_no_deriv _ _ hDer
          · rcases hPos i with ⟨p', hDer, _⟩
            exact zero_no_deriv _ _ hDer

theorem lfpDRS_noF_of_noFRegion
    {p : RunProc}
    {Q : ProcSet RunAct RunName}
    (hRegion : noFRegion p Q) :
    ∀ o, lfpDRS runEnv p Q o → ¬ rsObsCap .F o := by
  intro o hLfp
  exact hLfp rhoNoF rhoNoF_prefixpoint hRegion

-- ---------------------------------------------------------------------------

/-- `b0` refuses `a`, while `PBb0` enables it. -/
theorem lfpDRS_b0_PBb0_obs_neg_a :
    lfpDRS runEnv b0 {PBb0} obs_neg_a := by
  intro ρ hρ
  apply hρ
  change DRS runEnv ρ b0 {PBb0} (.node [] [.a])
  refine ⟨{PBb0}, fun i => False.elim (Fin.elim0 i), ?_, ?_, ?_, ?_⟩
  · intro i
    exact False.elim (Fin.elim0 i)
  · intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    exact b0_a_not_enabled
  · intro q hq
    have hq' : q = PBb0 := hq
    subst hq'
    exact ⟨.a, List.mem_cons.mpr (Or.inl rfl), PBb0_a_enabled⟩
  · intro q hq
    exact Or.inl hq

theorem lfpDRSAbsExactCanon_b0_PBb0_eq_singleton_F :
    ∀ c, lfpDRSAbsExactCanon runEnv b0 {PBb0} c ↔ c = .F := by
  have hNoS : ¬ lfpDRSAbsExactCanon runEnv b0 {PBb0} .S := by
    intro hS
    rcases minimalCap_left _ hS with ⟨o, hLfp, hCapS⟩
    exact (lfpDRS_noS_of_noSRegion (p := b0) (Q := {PBb0})
      (Or.inr <| Or.inl ⟨rfl, rfl⟩) o hLfp) hCapS
  have hNoT : ¬ lfpDRSAbsExactCanon runEnv b0 {PBb0} .T := by
    intro hT
    rcases minimalCap_left _ hT with ⟨o, hLfp, hCapT⟩
    have hCapS : rsObsCap .S o := capLe_trans hCapT (by simp [capLe])
    exact (lfpDRS_noS_of_noSRegion (p := b0) (Q := {PBb0})
      (Or.inr <| Or.inl ⟨rfl, rfl⟩) o hLfp) hCapS
  have hF : lfpDRSAbsExactCanon runEnv b0 {PBb0} .F := by
    have hDiff : abstractFailsAt (lfpDRSAbsExactCanon runEnv) .F b0 {PBb0} := by
      refine (abstractFailsAtExact_iff_rsDifferenceThreshold
        (env := runEnv) (N := .F) (p := b0) (Q := {PBb0})).2 ?_
      exact ⟨obs_neg_a,
        (rsDifferenceToSet_eq_lfpDRS runEnv b0 {PBb0} obs_neg_a).2
          lfpDRS_b0_PBb0_obs_neg_a,
        rsObsCap_F_obs_neg_a⟩
    rcases hDiff with ⟨d, hd, hdLe⟩
    cases d with
    | T => exact False.elim (hNoT hd)
    | S => cases hdLe
    | F => simpa using hd
    | RS => cases hdLe
  intro c
  constructor
  · intro hc
    cases c with
    | T => exact False.elim (hNoT hc)
    | S => exact False.elim (hNoS hc)
    | F => rfl
    | RS =>
        have hRawF := minimalCap_left _ hF
        have hRSLeF : capLe .RS .F := hc.2 .F hRawF (by simp [capLe])
        cases hRSLeF
  · intro hc
    simpa [hc] using hF

-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 1. PA ≰_F PB via the witness ⟨a⟩¬b
-- ---------------------------------------------------------------------------

/-- `⟨a⟩¬b` distinguishes `PA` from `PB`. -/
theorem lfpDRS_PA_PB_obs_a_neg_b :
    lfpDRS runEnv PA {PB} obs_a_neg_b := by
  intro ρ hρ
  apply hρ
  change DRS runEnv ρ PA {PB} (.node [(.a, obs_neg_b)] [])
  refine ⟨(fun _ => False), (fun _ r => r = PB), ?_, ?_, ?_, ?_⟩
  · intro i
    rcases i with ⟨val, hval⟩
    cases val with
    | zero =>
        refine ⟨PA, PA_a_PA, ?_⟩
        have hChild : ρ PA (DerivSetOf runEnv {PB} .a) obs_neg_b := by
          apply hρ
          change DRS runEnv ρ PA (DerivSetOf runEnv {PB} .a) (.node [] [.b])
          refine ⟨DerivSetOf runEnv {PB} .a, fun i => False.elim (Fin.elim0 i), ?_, ?_, ?_, ?_⟩
          · intro i
            exact False.elim (Fin.elim0 i)
          · intro x hx
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            subst hx
            exact PA_b_not_enabled
          · intro q hq
            rcases hq with ⟨r, hr, hDer⟩
            have hr' : r = PB := hr
            subst hr'
            cases hDer with
            | var hInner =>
              cases hInner
              exact ⟨RunAct.b, List.mem_cons.mpr (Or.inl rfl), PBb0_b_enabled⟩
          · intro q hq
            exact Or.inl hq
        simpa using hChild
    | succ val =>
      simp at hval
  · intro x hb
    exact nomatch hb
  · intro q hqneg
    exact False.elim hqneg
  · intro q hq
    right
    exact ⟨⟨0, by simp⟩, hq⟩

/-- The exact-pruned canonical abstraction still witnesses `PA ≰_F PB`. -/
theorem abstractRSDiffExact_PA_PB_at_F :
    abstractFailsAt (lfpDRSAbsExactCanon runEnv) .F PA {PB} := by
  refine (abstractFailsAtExact_iff_rsDifferenceThreshold
    (env := runEnv) (N := .F) (p := PA) (Q := {PB})).2 ?_
  exact ⟨obs_a_neg_b, (rsDifferenceToSet_eq_lfpDRS runEnv PA {PB} obs_a_neg_b).2
    lfpDRS_PA_PB_obs_a_neg_b, rsObsCap_F_obs_a_neg_b⟩

-- ---------------------------------------------------------------------------
-- 3. PB ≰_S PA via the witness ⟨a⟩(⟨a⟩⊤ ∧ ⟨b⟩⊤)
-- ---------------------------------------------------------------------------

/-- The branching node `⟨a⟩⊤ ∧ ⟨b⟩⊤` distinguishes `PBb0` from the `a`-successors of `PA`. -/
theorem lfpDRS_PBb0_DerivPAa_obs_split_ab :
    lfpDRS runEnv PBb0 (DerivSetOf runEnv {PA} .a) obs_split_ab := by
  intro ρ hρ
  apply hρ
  change DRS runEnv ρ PBb0 (DerivSetOf runEnv {PA} .a)
    (.node [(.a, .tt), (.b, .tt)] [])
  refine ⟨(fun _ => False), ?_, ?_, ?_, ?_, ?_⟩
  · intro i r
    match i.1 with
    | 0 => exact r = b0
    | 1 => exact r = PA
    | n + 2 => exact False
  · intro i
    rcases i with ⟨n, hn⟩
    cases n with
    | zero =>
        refine ⟨PBb0, ?_, ?_⟩
        · simpa using PBb0_a_PBb0
        · have hChild : ρ PBb0 (DerivSetOf runEnv {b0} .a) .tt := by
            apply hρ
            intro q hq
            rcases hq with ⟨r, hr, hDer⟩
            subst hr
            exact b0_a_not_enabled ⟨q, hDer⟩
          simpa using hChild
    | succ n =>
        cases n with
        | zero =>
            refine ⟨.zero, ?_, ?_⟩
            · simpa using PBb0_b_zero
            · have hChild : ρ (.zero : RunProc) (DerivSetOf runEnv {PA} .b) .tt := by
                apply hρ
                intro q hq
                rcases hq with ⟨r, hr, hDer⟩
                subst hr
                exact PA_b_not_enabled ⟨q, hDer⟩
              simpa using hChild
        | succ n =>
            have hge : 2 ≤ n.succ.succ := by
              exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
            exact False.elim (Nat.not_lt_of_ge hge hn)
  · intro x hb
    exact nomatch hb
  · intro q hqneg
    exact False.elim hqneg
  · intro q hq
    rcases hq with ⟨r, hr, hDer⟩
    have hr' : r = PA := hr
    subst hr'
    rcases PA_deriv_cases hDer with ⟨_, hCase⟩
    rcases hCase with rfl | rfl
    · right
      exact ⟨⟨1, by decide⟩, rfl⟩
    · right
      exact ⟨⟨0, by decide⟩, rfl⟩

/-- `⟨a⟩(⟨a⟩⊤ ∧ ⟨b⟩⊤)` distinguishes `PB` from `PA`. -/
theorem lfpDRS_PB_PA_obs_a_split_ab :
    lfpDRS runEnv PB {PA} obs_a_split_ab := by
  intro ρ hρ
  apply hρ
  change DRS runEnv ρ PB {PA} (.node [(.a, obs_split_ab)] [])
  refine ⟨(fun _ => False), (fun _ r => r = PA), ?_, ?_, ?_, ?_⟩
  · intro i
    rcases i with ⟨val, hval⟩
    cases val with
    | zero =>
        refine ⟨PBb0, PB_a_PBb0, ?_⟩
        have hChild : ρ PBb0 (DerivSetOf runEnv {PA} .a) obs_split_ab := by
          exact lfpDRS_PBb0_DerivPAa_obs_split_ab ρ hρ
        simpa using hChild
    | succ val =>
      simp at hval
  · intro x hb
    exact nomatch hb
  · intro q hqneg
    exact False.elim hqneg
  · intro q hq
    right
    exact ⟨⟨0, by simp⟩, hq⟩

/-- The exact-pruned canonical abstraction still witnesses `PB ≰_S PA`. -/
theorem abstractRSDiffExact_PB_PA_at_S :
    abstractFailsAt (lfpDRSAbsExactCanon runEnv) .S PB {PA} := by
  refine (abstractFailsAtExact_iff_rsDifferenceThreshold
    (env := runEnv) (N := .S) (p := PB) (Q := {PA})).2 ?_
  exact ⟨obs_a_split_ab,
    (rsDifferenceToSet_eq_lfpDRS runEnv PB {PA} obs_a_split_ab).2
      lfpDRS_PB_PA_obs_a_split_ab,
    rsObsCap_S_obs_a_split_ab⟩

-- ---------------------------------------------------------------------------
-- Canonical exact singleton values used in the paper
-- ---------------------------------------------------------------------------

theorem lfpDRSAbsExactCanon_PBb0_DerivPAa_eq_singleton_S :
    ∀ c,
      lfpDRSAbsExactCanon runEnv PBb0
        (DerivSetOf runEnv {PA} .a) c ↔ c = .S := by
  let Qa : ProcSet RunAct RunName := DerivSetOf runEnv {PA} .a
  have hQaPA : Qa PA := by
    exact ⟨PA, rfl, PA_a_PA⟩
  have hQab0 : Qa b0 := by
    exact ⟨PA, rfl, PA_a_b0⟩
  have hNoF : ¬ lfpDRSAbsExactCanon runEnv PBb0 Qa .F := by
    intro hF
    rcases minimalCap_left _ hF with ⟨o, hLfp, hCapF⟩
    exact (lfpDRS_noF_of_noFRegion (p := PBb0) (Q := Qa)
      (Or.inr <| Or.inl ⟨rfl, hQaPA, hQab0⟩) o hLfp) hCapF
  have hNoT : ¬ lfpDRSAbsExactCanon runEnv PBb0 Qa .T := by
    intro hT
    rcases minimalCap_left _ hT with ⟨o, hLfp, hCapT⟩
    have hCapF : rsObsCap .F o := capLe_trans hCapT (by simp [capLe])
    exact (lfpDRS_noF_of_noFRegion (p := PBb0) (Q := Qa)
      (Or.inr <| Or.inl ⟨rfl, hQaPA, hQab0⟩) o hLfp) hCapF
  have hS : lfpDRSAbsExactCanon runEnv PBb0 Qa .S := by
    have hDiff : abstractFailsAt (lfpDRSAbsExactCanon runEnv) .S PBb0 Qa := by
      refine (abstractFailsAtExact_iff_rsDifferenceThreshold
        (env := runEnv) (N := .S) (p := PBb0) (Q := Qa)).2 ?_
      exact ⟨obs_split_ab,
        (rsDifferenceToSet_eq_lfpDRS runEnv PBb0 Qa obs_split_ab).2
          (by simpa [Qa] using lfpDRS_PBb0_DerivPAa_obs_split_ab),
        rsObsCap_S_obs_a_split_ab⟩
    rcases hDiff with ⟨d, hd, hdLe⟩
    cases d with
    | T => exact False.elim (hNoT hd)
    | S => simpa using hd
    | F => cases hdLe
    | RS => cases hdLe
  intro c
  constructor
  · intro hc
    cases c with
    | T => exact False.elim (by simpa [Qa] using hNoT hc)
    | S => rfl
    | F => exact False.elim (by simpa [Qa] using hNoF hc)
    | RS =>
        have hRawS := minimalCap_left _ hS
        have hRSLeS : capLe .RS .S := hc.2 .S hRawS (by simp [capLe])
        cases hRSLeS
  · intro hc
    simpa [Qa, hc] using hS

theorem lfpDRSAbsExactCanon_PA_PB_eq_singleton_F :
    ∀ c, lfpDRSAbsExactCanon runEnv PA {PB} c ↔ c = .F := by
  have hNoS : ¬ lfpDRSAbsExactCanon runEnv PA {PB} .S := by
    intro hS
    rcases minimalCap_left _ hS with ⟨o, hLfp, hCapS⟩
    exact (lfpDRS_noS_of_noSRegion (p := PA) (Q := {PB})
      (Or.inl ⟨rfl, Or.inl rfl⟩) o hLfp) hCapS
  have hNoT : ¬ lfpDRSAbsExactCanon runEnv PA {PB} .T := by
    intro hT
    rcases minimalCap_left _ hT with ⟨o, hLfp, hCapT⟩
    have hCapS : rsObsCap .S o := capLe_trans hCapT (by simp [capLe])
    exact (lfpDRS_noS_of_noSRegion (p := PA) (Q := {PB})
      (Or.inl ⟨rfl, Or.inl rfl⟩) o hLfp) hCapS
  have hF : lfpDRSAbsExactCanon runEnv PA {PB} .F := by
    rcases abstractRSDiffExact_PA_PB_at_F with ⟨d, hd, hdLe⟩
    cases d with
    | T => exact False.elim (hNoT hd)
    | S => cases hdLe
    | F => simpa using hd
    | RS => cases hdLe
  intro c
  constructor
  · intro hc
    cases c with
    | T => exact False.elim (hNoT hc)
    | S => exact False.elim (hNoS hc)
    | F => rfl
    | RS =>
        have hRawF := minimalCap_left _ hF
        have hRSLeF : capLe .RS .F := hc.2 .F hRawF (by simp [capLe])
        cases hRSLeF
  · intro hc
    simpa [hc] using hF

theorem lfpDRSAbsExactCanon_PB_PA_eq_singleton_S :
    ∀ c, lfpDRSAbsExactCanon runEnv PB {PA} c ↔ c = .S := by
  have hNoF : ¬ lfpDRSAbsExactCanon runEnv PB {PA} .F := by
    intro hF
    rcases minimalCap_left _ hF with ⟨o, hLfp, hCapF⟩
    exact (lfpDRS_noF_of_noFRegion (p := PB) (Q := {PA})
      (Or.inl ⟨rfl, rfl⟩) o hLfp) hCapF
  have hNoT : ¬ lfpDRSAbsExactCanon runEnv PB {PA} .T := by
    intro hT
    rcases minimalCap_left _ hT with ⟨o, hLfp, hCapT⟩
    have hCapF : rsObsCap .F o := capLe_trans hCapT (by simp [capLe])
    exact (lfpDRS_noF_of_noFRegion (p := PB) (Q := {PA})
      (Or.inl ⟨rfl, rfl⟩) o hLfp) hCapF
  have hS : lfpDRSAbsExactCanon runEnv PB {PA} .S := by
    rcases abstractRSDiffExact_PB_PA_at_S with ⟨d, hd, hdLe⟩
    cases d with
    | T => exact False.elim (hNoT hd)
    | S => simpa using hd
    | F => cases hdLe
    | RS => cases hdLe
  intro c
  constructor
  · intro hc
    cases c with
    | T => exact False.elim (hNoT hc)
    | S => rfl
    | F => exact False.elim (hNoF hc)
    | RS =>
        have hRawS := minimalCap_left _ hS
        have hRSLeS : capLe .RS .S := hc.2 .S hRawS (by simp [capLe])
        cases hRSLeS
  · intro hc
    simpa [hc] using hS

end EqCheckingAbstractInterpretation.Ready.RunningExample
