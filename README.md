# Process Equivalence Checking as Abstract Interpretation

This repository contains a Lean formalization of how [generalized equivalence checking of process behaviors](https://generalized-equivalence-checking.equiv.io/) can be viewed as a form of abstract interpretation.

## Project Structure

- **EqCheckingAbstractInterpretation/**
  - **CCS/**: Core CCS syntax and operational semantics.
    - `Basic.lean`: Processes, environments, derivatives, and enabled-action predicates.
  - **Trace/**: Trace semantics, concrete/abstract transformers, correctness, and running example.
    - `Basic.lean`: Traces, denotational trace sets, trace difference, preorder, and equivalence.
    - `ConcreteTransformer.lean`: Concrete predecessor transformer `DTr` and least fixpoint `lfpDTr`.
    - `AbstractTransformer.lean`: Non-emptiness abstraction and abstract transformer `DTrSharp` with `AbstractDiff := lfpDTrSharp`.
    - `Correctness.lean`: Correctness bridge between abstract markers and concrete trace-difference non-emptiness, plus preorder/equivalence characterizations.
    - `RunningExample.lean`: Concrete CCS running example for trace-level results.
  - **Ready/**: Ready-simulation differences and capability-threshold abstraction.
    - `Basic.lean`: Capability lattice (`T,S,F,RS`), abstraction/concretization interface, generic threshold theorems, and concrete RS observation syntax (`RSObs`) with its capability classifier.
    - `ConcreteTransformer.lean`: Concrete RS predecessor transformer `DRS` and least fixpoint `lfpDRS`.
    - `AbstractTransformer.lean`: Exact abstract transformer `bestDRS` and abstract least-fixpoint objects (`lfpBestDRS`, canonical concrete-induced abstractions).
    - `Correctness.lean`: RS instantiation/correctness theorems, including canonical-lfp threshold exactness and `lfpBestDRS` alignment.
    - `ConcreteDifference.lean`: Concrete RS difference object `RSDifferenceToSet` and witness-preorder emptiness bridge.
    - `Denotational.lean`: Independent denotational characterization via finite certificates and equivalence theorem `rsDifferenceDenotational_eq_lfpDRS`.
    - `RunningExample.lean`: Concrete RS running example witnessing fragment-level failures.

- **EqCheckingAbstractInterpretation.lean**: Aggregates components of the project.

- **Main.lean**: Minimal executable entry point (currently a placeholder message).

- **lakefile.lean**: Configuration file for the Lake build system.

- **lean-toolchain**: Specifies the Lean version and toolchain for the project.

## Setup Instructions

1. Ensure you have the Lean toolchain installed as specified in the `lean-toolchain` file.
2. Use the Lake build system to build the project. Run the following command in the project directory:
   ```
   lake build
   ```
3. To run the main application, execute:
   ```
   lake run
   ```

## Documentation

The GitHub Pages workflow builds Lean API documentation with `doc-gen4` and publishes it under the deployed site `docs/` path to <https://eq-checking-as-abstract-interpretation.equiv.io/>.

## Current Formalization Scope

The formalization currently covers three layers.

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

All of these modules are re-exported by `EqCheckingAbstractInterpretation.lean`.

One remaining representational gap is intentional: `Ready/Basic.lean` encodes conjunction branches and refusals in `RSObs` as lists, while the paper presents them set-theoretically. So order/duplication invariance is handled mathematically in the paper, but is not quotiented in the Lean syntax.
