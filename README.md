# Process Equivalence Checking as Abstract Interpretation

This repository contains a Lean formalization of how [generalized equivalence checking of process behaviors](https://generalized-equivalence-checking.equiv.io/) can be viewed as a form of abstract interpretation.

## Project Structure

- `EqCheckingAbstractInterpretation/CCS/`: CCS semantics and finite transition systems.
- `EqCheckingAbstractInterpretation/FiniteEvaluator/`: Shared finite evaluation machinery.
- `EqCheckingAbstractInterpretation/Trace/`: Trace semantics and evaluation.
- `EqCheckingAbstractInterpretation/Ready/`: Ready-simulation semantics and evaluation.
- `EqCheckingAbstractInterpretation.lean`: Re-exports the formalization.
- `Main.lean`: CSV-driven trace and Ready comparison executable.
- `lakefile.lean` and `lean-toolchain`: Build configuration and Lean version.

## Setup Instructions

1. Ensure you have the Lean toolchain installed as specified in the `lean-toolchain` file.
2. Use the Lake build system to build the project. Run the following command in the project directory:
   ```
   lake build
   ```
3. To compare two states in a CSV transition system, execute:
   ```
  lake exe Main <trace|ready> <transitions.csv> <left-state> <right-state>
   ```
  Transition rows contain `source-state-id,target-state-id,transition-label`.
  A state may also have a `state-id,state-name,annotation` row; names contain letters
  and must be unique. State arguments may be non-negative IDs or names from the CSV.
  In `trace` mode, the executable prints a Boolean trace-preorder decision:
  ```
  lake exe Main trace assets/peterson_mutex_5_15.csv 5 15
  lake exe Main trace assets/ltbts1.csv L27 R27
  ```
  In `ready` mode, it lists the preorders that hold from the left state to the right:
  ```
  lake exe Main ready tests/ready_modes.csv Left Right
  # Holding preorders for (Left, Right): trace, failures
  ```
  The Ready hierarchy consists of trace, simulation, failures, and ready simulation.
  A preorder holds when no minimal distinguishing capability is below its threshold;
  `none` means none of the four hold.

Run the executable interface regression test with `bash tests/main.sh`.

## Documentation

The GitHub Pages workflow builds Lean API documentation with `doc-gen4` and publishes it under the deployed site `docs/` path to <https://eq-checking-as-abstract-interpretation.equiv.io/>.

## Current Formalization Scope

The formalization currently covers four layers.

1. Trace semantics and trace equivalence.
  - `Trace/Basic.lean` defines traces, trace difference, preorder, and equivalence.
  - `Trace/ConcreteTransformer.lean` defines the concrete predecessor transformer `DTr`, its least fixpoint `lfpDTr`, and proves the concrete/lfp correspondence.
  - `Trace/AbstractTransformer.lean` defines the abstract marker system via `AbstractDiff := lfpDTrSharp`.
  - `Trace/Correctness.lean` proves marker/non-emptiness correctness and preorder/equivalence characterization theorems.

2. Concrete ready-simulation differences.
  - `Ready/ConcreteTransformer.lean` defines the concrete predecessor transformer `DRS` and its least fixpoint `lfpDRS`.
  - `Ready/ConcreteDifference.lean` defines the concrete RS difference object `RSDifferenceToSet` from `lfpDRS`.
  - `Ready/Denotational.lean` gives an independent denotational characterization `rsDifferenceDenotational` and proves `rsDifferenceDenotational_eq_lfpDRS`.

3. Unified capability-threshold abstraction.
  - `Ready/Basic.lean` formalizes the capability lattice and generic threshold theorems (`..._of_alpha`, `..._of_lfp`).
  - `Ready/AbstractTransformer.lean` defines the exact abstract transformer (`bestDRS`) and abstract lfp constructions (`lfpBestDRS`, `lfpDRSAbsCanon`, `lfpDRSAbsExactCanon`).
  - `Ready/Correctness.lean` proves RS instantiation theorems, including canonical-lfp threshold exactness and `lfpBestDRS` equivalence results.

4. Executable finite evaluation and correctness.
  - `FiniteEvaluator/Basic.lean` and `FiniteEvaluator/Correctness.lean` provide shared finite saturation and its proof.
  - `CCS/FiniteLTS.lean` defines the realization conditions relating finite transition tables to CCS derivatives.
  - `Trace/FiniteEvaluator.lean` and `Trace/FiniteEvaluatorCorrectness.lean` implement trace queries and connect them to CCS trace semantics for realized systems.
  - `Ready/FiniteEvaluator.lean` and `Ready/FiniteEvaluatorCorrectness.lean` implement capability and threshold queries and prove their exact correspondence to `lfpDRSAbsExactCanon` and `abstractFailsAt` for realized systems.
  - `Ready/RunningExample.lean` proves realization of its finite table and applies the generic Ready correctness theorems to its computed results.

All of these modules are re-exported by `EqCheckingAbstractInterpretation.lean`.

One remaining representational gap is intentional: `Ready/Basic.lean` encodes conjunction branches and refusals in `RSObs` as lists, while the paper presents them set-theoretically. So order/duplication invariance is handled mathematically in the paper, but is not quotiented in the Lean syntax.
