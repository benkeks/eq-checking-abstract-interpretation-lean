import EqCheckingAbstractInterpretation.Ready.ConcreteTransformer

namespace EqCheckingAbstractInterpretation.Ready

open EqCheckingAbstractInterpretation.CCS

universe u v

variable {Action : Type u} {Name : Type v}

/--
Concrete RS difference relation used in the current mechanization.
At this stage it is taken to be the least model of the concrete predecessor
transformer `DRS`.
-/
def RSDifferenceToSet
    (env : Env Action Name) :
    DiffSysRS Action Name (RSObs Action) :=
  lfpDRS env

/-- By definition of `RSDifferenceToSet`, the lfp characterization is immediate. -/
theorem rsDifferenceToSet_eq_lfpDRS
    (env : Env Action Name)
    (p : CCS Action Name)
    (Q : ProcSet Action Name)
    (o : RSObs Action) :
    RSDifferenceToSet env p Q o ↔ lfpDRS env p Q o := by
  rfl

/-- Witness-preorder induced by RS difference lfp emptiness. -/
def RSWitnessPreorder
    (env : Env Action Name)
    (p q : CCS Action Name) : Prop :=
  ¬ ∃ o : RSObs Action, lfpDRS env p {q} o

/-- Corollary: witness-preorder equals emptiness of concrete RS difference. -/
theorem rsWitnessPreorder_iff_rsDiffEmpty
    (env : Env Action Name)
    (p q : CCS Action Name) :
    RSWitnessPreorder env p q ↔
      ¬ ∃ o : RSObs Action, RSDifferenceToSet env p {q} o := by
  rfl

end EqCheckingAbstractInterpretation.Ready
