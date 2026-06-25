# Process Equivalence Checking as Abstract Interpretation

This project implements a Lean autoformalization of how [generalized equivalence checking of process behaviors](https://generalized-equivalence-checking.equiv.io/) can be understood as a form of abstract interpretation.

## Project Structure

- **EqCheckingAbstractInterpretation/**
  - **Trace/**: CCS trace semantics and trace relations.
    - `Basic.lean`: Direct CCS formalization (syntax, environments, derivative relation, denotational trace set), plus trace difference, trace preorder, and trace equivalence.
    - `AbstractTransformer.lean`: Abstract non-emptiness transformer `DTrSharp`, with `AbstractDiff` defined as its least fixpoint.
    - `Correctness.lean`: Soundness/completeness proofs connecting marker presence and concrete non-empty trace difference; preorder/equivalence characterization theorems.
    - `Examples.lean`: Small concrete CCS examples (preorder and non-equivalence).
    - `CorrectnessExamples.lean`: Toy instantiations and restricted-fragment bridge examples.
  - **Ready/**: Capability-threshold formalization for the unified section.
    - `Observations.lean`: Concrete ready-observation syntax (`RSObs`) and induced capability classifier.
    - `ConcreteTransformer.lean`: Concrete RS predecessor transformer (`DRS`) and least-fixpoint layer (`lfpDRS`, canonical abstract lfp view).
    - `ConcreteDifference.lean`: Current concrete RS difference object and preorder-emptiness bridge, defined from `lfpDRS`.
    - `Denotational.lean`: Independent denotational characterization of RS differences via finite certificates; equivalence to lfp (`rsDifferenceDenotational_eq_lfpDRS`).
    - `Unified.lean`: Capability lattice (`T,S,F,RS`), capability abstraction/concretization interface, monotonicity condition for observation fragments, and threshold correctness theorems (`..._of_alpha`, `..._of_lfp`).
    - `ConcreteObservations.lean`: Instantiation theorems for the concrete RS syntax, including an assumption-free canonical-lfp instance.
  - **CFG/**: Contains definitions and functions related to control flow graphs.
    - `Basic.lean`: Basic definitions for CFG.
  - **AbstractInterpretation/**: Core definitions and functions for abstract interpretation.
    - `Basic.lean`: Basic definitions for abstract interpretation.
  - **Equivalence/**: Defines concepts and functions related to equivalence.
    - `Basic.lean`: Basic definitions for equivalence.

- **EqCheckingAbstractInterpretation.lean**: Aggregates components of the project.

- **Main.lean**: Entry point of the application, executing the abstract interpretation and equivalence checking.

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

GitHub Pages publishes the Lean API documentation at <https://benkeks.github.io/eq-checking-abstract-interpretation-lean/docs/EqCheckingAbstractInterpretation/> via a `doc-gen4` build in the GitHub Pages workflow.

## Current Formalization Scope

The formalization currently covers three layers.

1. Trace semantics and trace equivalence.
  - `Trace/Basic.lean` defines CCS traces, trace difference, preorder, and equivalence.
  - `Trace/AbstractTransformer.lean` defines the abstract marker system via `AbstractDiff := lfpDTrSharp`.
  - `Trace/Correctness.lean` proves the marker/non-emptiness and preorder/equivalence correctness theorems.

2. Concrete ready-simulation differences.
  - `Ready/ConcreteTransformer.lean` defines the concrete predecessor transformer `DRS` and its least fixpoint `lfpDRS`.
  - `Ready/ConcreteDifference.lean` packages the concrete RS difference as `RSDifferenceToSet`.
  - `Ready/Denotational.lean` gives an independent denotational characterization `rsDifferenceDenotational` and proves `rsDifferenceDenotational_eq_lfpDRS`.

3. Unified capability-threshold abstraction.
  - `Ready/Unified.lean` formalizes the capability lattice and the generic threshold theorems.
  - `Ready/Observations.lean` and `Ready/ConcreteObservations.lean` instantiate that framework for the concrete RS observation syntax.
  - The generic theorem is assumption-explicit; the canonical lfp-based concrete instance is assumption-free.

All of these modules are re-exported by `EqCheckingAbstractInterpretation.lean`.

One remaining representational gap is intentional: `Ready/ConcreteObservations.lean` uses lists for conjunction branches and refusals, while the paper writes them set-theoretically. So order/duplication invariance is treated mathematically in the paper, but not quotiented in the Lean syntax.

## Usage

After building the project, you can modify the Lean files in the `EqCheckingAbstractInterpretation` directory to implement your own abstract interpretation logic or equivalence checking algorithms.
