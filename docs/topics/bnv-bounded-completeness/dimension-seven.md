# First Gate: Completeness Through Dimension Seven

## Frozen Physical Scope

Use the ten signed SM fermion species and H/H-conjugate. Their dimension
weights are 3 and 2 respectively in units of twice the engineering dimension.
Bound total weight by 14. BNV means nonzero total baryon grading, not an
initial assumption of Delta B = 1 or of any particular lepton grading.
Coefficients are gauge- and Lorentz-invariant algebraic scalar functionals
with antisymmetry on repeated fermions and symmetry on repeated bosons.
No field strengths, derivatives, EOM/IBP identifications or equations of
motion enter this coefficient space. A single Higgs doublet is fixed; its
residual representation must be specified, not silently assumed trivial.

For generic H, use specified compatible representations on flavor carriers.
Preserve arbitrary multiplicities where the existing quotient/Hom proofs
permit them. Any finite-dimensional requirement of a local factorization or
actual-field bridge must be explicit and attached to that theorem, not added
silently to the whole program. Finite charge tests may use finite bases.

## Statements To Establish

1. **Independent bounded input.** Define a coefficient space from the entire
   weighted alphabet before enumerating allowed families. Encode scalar
   Bose statistics and fermion exterior statistics in a mixed carrier.
2. **Support theorem.** Derive all admissible field contents using gauge
   weights, color triality and left/right Weyl conditions, with kernel-checked
   bounded arithmetic where appropriate. Necessity filters alone are not
   sufficiency or completeness. Prove no BNV contributions below six and
   identify the six- and seven-dimensional supports, including conjugates.
3. **Per-family completeness.** Prove local invariant factorization and
   statistics relations for every surviving dimension-seven type. Produce
   explicit residual Hom spaces with two-sided extraction/reconstruction.
4. **Whole-space decomposition.** Prove the independently defined bounded
   coefficient space is linearly equivalent to the finite product of the
   complete residual spaces. Boson/conjugate-field identifications and
   nontrivial Higgs residual action must remain visible.
5. **Total prohibition criterion.** If C is that coefficient space and
   R_t its classified residual factors, prove
   `Subsingleton C ↔ ∀ t, Subsingleton R_t`, equivalently every coefficient
   vanishes iff every factor vanishes. Prove existential nonzero allowance
   iff some residual factor has a nonzero element. This concerns existence
   of permitted coefficients, not a particular UV model generating them.
6. **Application controls.** Transport through supplied actual-field
   identifications; give a finite cyclic example forbidding all bounded
   contributions and a positive example with an explicit nonzero coefficient.
   Keep the general arbitrary-H criterion separate from a charge algorithm.

The existence test on residual Hom is not claimed to be algorithmically
decidable for every arbitrary group H.

## Candidate Inventory, Not A Premise

Heeck–Le v2 Section 7 lists four non-derivative dimension-seven types:
`H-tilde L-bar u d²`, `H-tilde L-bar d Q²`,
`H-tilde e-bar d² Q`, and `L-bar d³ H`.
Translate tilde, barred carriers and right-handed species using explicit
algebraic identifications. In particular, H-tilde and H-dagger are not new
independent physical Higgs species. Determine the proper dual/conjugate
carriers and signs before asserting expression agreement.

The expected Delta B = +1, Delta L = -1 grading and four-type list must be
derived from the alphabet; failure to agree is investigated, not hidden by
restricting the initial domain. The source uses three generations; our desired
arbitrary-multiplicity classification requires its own proofs and may need
additional relations or different representative counts.

## Reuse And Acceptance

Reuse the dimension-six signed decomposition, exterior weight support,
Weinberg mixed-statistics descent, arbitrary-slot statistics quotients,
finite local dictionaries and residual selection criteria. The new five-field
mixed carrier and its actual inverse are the main first integration test.

The gate passes only when all six statement groups above have proofs and
verification, with no literature completeness axiom or unproved dictionary
premise. A conditional factorization framework alone does not pass. If an
essential large new foundation is discovered, record the exact missing
statement and request a scope decision instead of calling the gate complete.

## Completed Acceptance Evidence

All six statement groups are discharged in the
[dimension-seven proof dossier](../../proof/current/applications/Physics/BNV_SEVEN_COMPLETENESS.md).
The input/support and degree theorems derive the allowed degrees and species;
signed local coordinates supply the invariant dictionaries and typed exchange
descent. `BnvSevenCompleteness.equiv` assembles the independent whole input,
with inverse and prohibition/nonzero iff proofs. `BnvSevenModelInterface`
constructs actual-field transport, and `BnvSevenControls` supplies both cyclic
controls. This is the current stop gate; it does not accept dimensions eight
through eleven by analogy.
