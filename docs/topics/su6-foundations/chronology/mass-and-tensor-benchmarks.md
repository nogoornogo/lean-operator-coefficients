# Mass-source review and tensor benchmarks

Checkpoint record.
Claims and commands below describe their original checkpoint, not a new build
or current instructions. Do not append new work here; use topic records.

- Reviewed `kilo` commit `checkpoint 01`: its Lean lemmas are valid conditional
  UV-support results, not radical-support proofs. Preserved them and merged
  with corrected scope/documentation in `checkpoint 02`.
- Added `AbelianActualSpectrum`: nonnegative actual character coefficients,
  faithful evaluation, eigenvector extraction, and dual orientation.
  `WeylZeroModeSupport` derives all fifteen actual SM radical sectors for
  positive generation index and `qque`/`duql` operator witnesses without
  `nonzeroOrbitProfiles`. Negative index gives conjugate zero modes.
- Added `InvariantLineMass` and `ConcreteWeylNonzeroMass`: the same
  `15 + 2 bar6` source admits a proved nonzero rank-one symmetric mass,
  with generation one and radical dimension 26. This directly refutes
  uniqueness of zero mass, but does not lift every extra mode.
- The new permanent audit constructs trivial- and finite-Abelian examples
  without support premises and reports only `propext`, `Classical.choice`,
  and `Quot.sound`. Both new and reviewed audits are wired into the root
  imports. Full build succeeds in 4171 jobs, with no new-module warnings
  or placeholders. General-hypercharge E remains Dirac-scoped.
- Completed the optional sign endpoint: `WeylConjugateOperator` constructs
  negative-index conjugate signatures, checks inverted residual character
  and signed baryon number, and proves that every nonzero generation index
  has an invariant witness in one of the two explicitly distinguished
  orientations. Permanent audit reports standard axioms; full build 4173 jobs.
- Strengthened the all-left-handed benchmark: faithful trace equality gives
  a prescribed eigenbasis, and a symmetric hyperbolic pairing removes six
  pairs from the actual `15 + 2 bar6` fields. The radical has dimension 15
  and full SM character, with no spectrum premise or extra singlets.
  Invariance remains the physical torus times the neutral residual action.
  The reusable basis/mass lemmas and permanent audit use standard axioms;
  full build 4177 jobs. The general-hypercharge E extension remains separate.
- Completed the algebraic/trace part of the dual-index B3 extension:
  antisymmetrization doubles the fifth moment, so a nonzero-generation dual
  SM target still fixes the standard cocharacter. One resolved dual target
  supplies both B3 and C1 -> C2, including torsion charges, without recovering
  self-dual sectors. The permanent audit uses standard axioms; full build
  4180 jobs. Canonical general-hypercharge mass-source assembly remains open.
- Completed that assembly in the declared symmetric linearized model class.
  Canonical nonnegative matter derives the UV trace, mass conservation
  transports the actual radical dual target, and one target supplies B3 and
  C1 -> C2. Actual nonnegative radical multiplicities provide zero-mode
  vectors and supported operators in both explicitly distinguished index
  orientations. `ContinuousWeylModel` composes A1 geometry; a new zero-mass
  one-generation constructor proves non-vacuity for arbitrary neutral H.
  `AuditContinuousWeylModel` checks constructors and standard axioms; full
  build 4185 jobs. The scope is torus/residual-group invariant linearized
  masses and operator signatures, not general Weyl Yukawa or amplitude
  semantics. All three listed NEXT STEPS are complete.
- Completed optional benchmark transport. Equality of the two actual field
  bundles, not merely trace equivalence, permits preserving any standard
  symmetric mass. The adapter preserves the radical representation and full
  actual spectrum. `ContinuousWeylFullMass` gives the nonzero 15-mode example
  in the continuous-geometry interface. Persistent audit reports standard
  axioms; full build 4190 jobs. Existing zero-mass examples are unchanged.
- Completed a scalar-linear symmetric Weyl Yukawa/VEV source adapter and
  composed it with E. Arbitrary-group invariance gives a tensor-product
  intertwiner, and a vacuum stabilizer supplies the unbroken mass without
  full-ambient vacuum invariance. Constructed a nonzero full-SU(6) tensor
  on `6 + 6*`, and a post-breaking zero-bare-mass/nonzero-Yukawa realization
  of the exact 15-mode benchmark. Audit includes finite Abelian and Majorana
  tests, and a zero-VEV regression. Standard axioms only; full build 4194 jobs.
  Full non-Abelian proton-operator tensors on the actual radical and general
  Lagrangian semantics remain separate tasks, not consequences of this step.
- Constructed actual ordered internal `qque` and `duql` gauge tensors on
  the standard SM field representations. Proved full covering-gauge
  invariance and nonzero values, and recovered the C2 residual characters
  from fieldwise tensor-product actions for arbitrary Abelian groups.
  Invariance iff trivial residual character and C1 -> C2 application are
  checked. Persistent audit includes a nontrivial finite-group compatible
  assignment and an incompatible assignment with sign-flipped witnesses.
  Standard axioms only; full build 4198 jobs. Actual-radical transport and
  Lorentz/Grassmann nonvanishing remain open. The existing torus-basis mass
  is not silently promoted to a full gauge-invariant mass.
- Constructed a decomposed full-gauge 27-dimensional mass benchmark with
  all-left-handed SM light fields and a six-dimensional heavy pair. Proved
  nonzero mass and a representation equivalence from its actual radical
  to the 15-dimensional SM space. Equivariant retractions, duals, and the
  bidual map transport nonzero ordered `qque`/`duql` tensors to that radical
  and its dual, retaining the exact C2 characters. Finite-group positive
  and negative audits use standard axioms only; full build 4203 jobs.
  This is not yet a lift of the canonical SU(6) field model. Full-gauge
  branching for the neutral benchmark and Lorentz/Grassmann semantics
  remain separate obligations; previous mass choices are unchanged.
