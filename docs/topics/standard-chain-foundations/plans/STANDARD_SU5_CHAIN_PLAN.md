# Standard SU(5) chain generalization

Archived checkpoint; not a current work queue. Consult the current topic records.

Updated: stage 02

## Current Status

**CHAIN-1 and CHAIN-2 are LEAN-CHECKED.** The actual arbitrary-SU(5)
source derives Weyl/profile compatibility from an exact dual radical target,
then constructs actual supported neutral signatures. The physical torus is
identified with the standard SM embedding, and its evaluator agrees exactly
with the legacy Fourier evaluator. The declaration
inventory and controls are in
[the formalization record](../../../proof/current/applications/GUT/interfaces/standard-su5-chain.md).
**CHAIN-3a is also LEAN-CHECKED.** The common ambient pullback theorem,
continuous and scalar-family wrappers, and an actual charged `10 + bar5`
inhabitant are constructed.
**The CHAIN-3b retained SU(5) adapter is LEAN-CHECKED.** It preserves arbitrary
generation mixing and supplied invariant masses, derives the dual target,
and proves exact full-spectrum equality for the retained zero-mass model.
Continuous actions give the physical wrapper. The stronger old full-tensor
endpoint remains available. **The CHAIN-3b SU(6) adapter is also LEAN-CHECKED.**
Every `ContinuousProfileModel.Model` converts using its already proved
hypercharge rigidity, with actual field isometry, preserved mass and radical,
and exact full-spectrum equality. Scalar-family evaluation is preserved;
descent of the scalar representation itself is not asserted. The old
interface has no topology on H, so the common continuous wrapper requires
explicit joint product-action continuity. **CHAIN-4 is now LEAN-CHECKED.**
The standard block family for every N >= 5, exact N = 5/6 compatibility,
and an actual continuous 42-dimensional SU(7) positive-target model are
checked; see [the family record](../../../proof/current/applications/GUT/interfaces/standard-su-n.md).
The roadmap is complete in its declared scope. The latest full regression
has 4437 jobs; all 1666 axiom-bearing reports use only the standard three axioms.

## Aim and Scope

Develop a common selection-rule theorem for actual finite-dimensional
matter restricted along the **standard SM -> SU(5) -> G chain**, rather
than independently repeating the SU(5)/SU(6) argument for every new group.
This is a conditional theorem about an explicitly supplied chain, not a
classification of all SM embeddings or hypercharges in G.

The intended inputs are an actual unitary G representation, a strict
commuting unitary action of an arbitrary Abelian residual group, an
invariant complex-bilinear symmetric mass on the unbroken group, and an
exact **dual radical character** target with five finite nonnegative SM
charge profiles of common positive total, plus singlets. Continuity is
retained in physically admissible model wrappers; algebraic core lemmas
should not assume it when unused. Group injectivity/continuity hypotheses
must be distinguished from weaker hypotheses sufficient for pullback.
The coefficient bridge reads characters on the physical SM torus times
the residual group. Full-SM mass invariance is a possible stronger wrapper
input, not something inferred from torus invariance.

The intended output is a supported neutral Delta B = 1 operator signature
and the failure of protection by the specified ordinary Abelian selection
rule. It is not a nonzero interaction coefficient, amplitude, proton
decay rate, or an assertion of exact SM vacuum stabilization. General
radical support must not be advertised as a full SM/Lorentz tensor theorem.
The existing retained-matter SU(5) tensor theorem keeps its own stronger
field-level output and narrower source assumptions.

## Milestones

### CHAIN-1: Shared Character and Mass Support

- Move the faithful finite-character polynomial evaluator and algebraic
  symmetric-mass quotient/index lemmas to genuinely group-independent
  modules, keeping declaration names and old imports usable.
- Use full character eigenspaces of an actual finite-dimensional unitary
  Abelian representation to construct nonnegative multiplicities directly,
  without the legacy trivial SU(6) spectator construction.
- Prove equality to the trace character, coefficient-level dual-index
  conservation, and actual nonzero radical vectors from positive dual
  coefficients. Prove agreement with the old spectrum.
- Audit transitive imports, axioms, zero mass, a nonzero mass, self-dual
  characters, and the necessity of positive rather than signed support.

### CHAIN-2: Standard SU(5) Source Bridge

- Reuse the existing SM coefficient/profile algebra and standard SU(5)
  embedding. Supply a faithful target evaluator and concrete Weyl
  conjugation compatibility without transitive SU(6) source dependence.
- Restrict actual arbitrary SU(5) matter with commuting residual action;
  derive target invariance from conjugation and dual-index conservation.
- Derive the Q/u/e and d/L profile equalities and then supported neutral
  signatures. Neither equalities nor support may be fields of the model.
- Retain and compare the old retained-matter SU(5) endpoint. Arbitrary
  source Laurent polynomiality is unnecessary if target faithfulness and
  source character invariance suffice.

### CHAIN-3: Ambient Composition

- Pull back actual G matter along an explicit SU(5) homomorphism and
  assemble the common theorem from CHAIN-1/2.
- Separate physical inclusion assumptions from algebraic pullback facts;
  add continuous model and evaluated scalar-family wrappers.
- Prove compatibility with applicable SU(5)/SU(6) standard-branch models.
  Preserve the independent flipped obstruction and the stronger SU(6)
  embedding/hypercharge results; do not replace them by weaker assumptions.

### CHAIN-4: Standard SU(N) Family

- Construct the standard block SU(5) inclusion for N >= 5 with the needed
  homomorphism, injectivity, unitarity, determinant, and continuity facts.
- Instantiate the common theorem and audit N = 5, N = 6, and a higher-rank
  example. These checks illustrate a universal proof, not sampling evidence.
- Record what remains conditional on the light target and the chosen chain.

## Verification and Preservation

Each proof milestone requires targeted audits, transitive dependency
checks for the shared core, full `lake build`, and an axiom scan allowing
only `propext`, `Classical.choice`, and `Quot.sound`. No dependency or
toolchain upgrade is part of this work. Keep old declarations and audits;
prefer compatibility theorems over replacing a definition silently.

Update the focused dossier and status records and commit each verified
theme. `ACTIVE.md` contains pending work only. Do not mark the whole chain
theorem complete merely because its shared algebraic core is complete.

Recovery tags created before this work (local, not pushed):

- `mass-profile-complete-stage 01`: `checkpoint 01`, current reviewed MASS/PROFILE
  baseline; recorded proof build 4392 jobs.
- `representation-generalizations-complete-stage 01`: `checkpoint 02`, reusable
  character restriction, exact character index, and U/SU multiplicity
  centralizer generalizations; historical recorded build 4255 jobs.

The latter A-C labels are the generalization review labels, not the
original SU(6) physical proof's lemma labels. Neither tag claims an
unconditional physical proton-decay theorem.
