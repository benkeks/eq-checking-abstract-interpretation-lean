namespace EqCheckingAbstractInterpretation.CCS

universe u v
variable {Action : Type u} {Name : Type v}

/-- CCS processes: action prefix, nondeterministic choice, deadlock `0`, and recursive variables. -/
inductive CCS (Action : Type u) (Name : Type v) where
  | prefix : Action → CCS Action Name → CCS Action Name
  | choice : CCS Action Name → CCS Action Name → CCS Action Name
  | zero : CCS Action Name
  | var : Name → CCS Action Name

/-- A recursive process environment maps each name to its defining CCS term. -/
abbrev Env (Action : Type u) (Name : Type v) := Name → CCS Action Name

abbrev ProcSet (Action : Type u) (Name : Type v) := CCS Action Name → Prop

instance : Singleton (CCS Action Name) (ProcSet Action Name) where
  singleton q := fun r => r = q

instance : EmptyCollection (ProcSet Action Name) where
  emptyCollection := fun _ => False

instance : Singleton (CCS Action Name) (CCS Action Name → Prop) where
  singleton q := fun r => r = q

instance : EmptyCollection (CCS Action Name → Prop) where
  emptyCollection := fun _ => False

/-- One-step labeled transition relation derived from the CCS structural rules
    and the recursive environment. -/
inductive Deriv (ρ : Env Action Name) : CCS Action Name → Action → CCS Action Name → Prop where
  | prefix {a p} : Deriv ρ (.prefix a p) a p
  | choice_left {p q a p'} : Deriv ρ p a p' → Deriv ρ (.choice p q) a p'
  | choice_right {p q a q'} : Deriv ρ q a q' → Deriv ρ (.choice p q) a q'
  | var {X a p'} : Deriv ρ (ρ X) a p' → Deriv ρ (.var X) a p'

/-- The set of `a`-successors of a single process `p`. -/
def DerivSet (ρ : Env Action Name) (p : CCS Action Name) (a : Action) : CCS Action Name → Prop :=
  fun p' => Deriv ρ p a p'

/-- The lifted derivative: the set of `a`-successors of any process in `P`. -/
def DerivSetOf (ρ : Env Action Name) (P : CCS Action Name → Prop) (a : Action) : CCS Action Name → Prop :=
  fun p' => ∃ p, P p ∧ Deriv ρ p a p'

/-- The set of actions immediately enabled at process `p`. -/
def Enabled (ρ : Env Action Name) (p : CCS Action Name) : Action → Prop :=
  fun a => ∃ p', Deriv ρ p a p'

end EqCheckingAbstractInterpretation.CCS
