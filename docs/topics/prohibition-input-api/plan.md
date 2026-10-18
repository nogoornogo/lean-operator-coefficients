# Frozen Implementation Plan

## 1. A Thin Prohibition Facade

Reuse Math.SelectionCriteria.Forbidden/Allowed, ProhibitionSpecification.Spec
and ComposableProtection.forbidden_iff. Introduce degree-wise and all-degree
input-side names over the existing actual supportSpace; avoid a new model
structure duplicating the local/residual field dictionaries.

Expose selected-content projection, monotonicity under smaller targets,
union/indexed-union equivalences and equivalence transport. All-degree
quantification must have no degree cutoff. Empty specifications and zero
carriers are legitimate, so prohibition must not imply a nonempty spectrum.

Acceptance: definitions unfold to current predicates; the factorwise iff is
an application of existing completeness, with no new completeness premise.

## 2. Representation Constraints on Each Selected Factor

Use the actual TypedMixedSeparatedHom.residual carrier, including local and
exchange relations, and its GradedMixedCompleteness.Factor. From Forbids
extract factor vanishing. Apply CommonIrreducible.all_zero_iff only with an
explicit IsSemisimpleRepresentation proof for that factor source.

Expose both a no-common-constituent condition and a contradiction consumer:
a selected factor with certified shared constituent defeats prohibition.
Do not replace the quotient carrier by a multiplicity tensor or assume every
raw field constituent survives the local/statistics quotient.

Acceptance: general group action; no unnecessary finite-dimensional premise.
Semisimplicity remains a named hypothesis when not supplied by an adapter.

## 3. Scalar-Character Necessity and Restriction Obstructions

First isolate a generic invariant-functional statement. For a representation
r of H on a complex carrier V with r(g)v = chi(g)q • v, and Nontrivial V,
prove that vanishing of Hom_H(V,C_trivial) is equivalent to existence of a
group element with chi(g)q != 1. The neutral direction requires construction
of an actual nonzero functional, using a basis/linear functional API; it is
not a dimension-count premise. If V is zero, only the sufficiency direction
survives. Record this negative control in source.

Connect to selected actual factors only through a proved scalar-action bridge
on their admitted quotient carrier and supplied/proved nontriviality. The API
must not assert that charge detection is necessary for arbitrary representations
or for a raw local tensor which has not survived statistics relations.

For symmetry restriction j:J->H, reuse the existing selected/factor restriction
maps. Prove the conditional obstruction: forbidden larger-group source plus
nonzero smaller-group target implies non-surjectivity. State separately from
Protected and its surjectivity characterization. The DGT flavor bridge offers
a concrete regression, without conflating dipole and mixed-field domains.

Acceptance: all extra premises visible in the theorem type. A scalar-neutral
zero-domain example refutes the unguarded converse. No new saturation theorem.

## 4. One Bounded Physics Consumer and Regressions

Add a thin input-side facade to the existing SM/Higgs specification adapter.
Use an already certified one-generation LLHH/scalar-flavor case to test a
nonzero-admission-dependent charge necessity statement. Reuse existing witness
and field equivalences rather than create new operator foundations.

Regression roles:

- Koren/BGW: existing sufficient simultaneous prohibition certificates can be
  expressed using the facade; do not turn their sufficient subgroup conditions
  into a full classification of models.
- DGT: actual selected flavor restriction can fail surjectivity while baryon
  protection persists. Dedicated dipole selectors stay in their own domain.
- Quarticity: original SM/Higgs L2 prohibition does not extend automatically
  to the nuR/eta alphabet. The dressed coefficient is a domain-change control.
- Generic zero carrier: neutral charge does not force nonzero existence.

Keep these finite deliverables. A full adaptor for every existing sector,
exhaustive necessary constraints on UV matter, and automatic searches are
future topics requiring their own scope decision.

## 5. Proof Acceptance and Documentation

Place reusable generic APIs and audits in Math; the SM/Higgs consumer in
Physics. Register sources in aggregates. Preserve dependency pins and strict
axiom allowances. Maintain the topic's results/verification, proof dossier and
assumptions ledger only as results become verified; do not list planned
necessity theorems as established assumptions.

Run focused source/audit builds, strict transitive axiom checks, one serialized
full lake build, layout/link checks and git diff --check. Review each converse
against its actual nontriviality, scalar-action and semisimplicity hypotheses.
Commit coherent verified milestones and continue to the frozen endpoint.
Stop for a scope decision if a new foundational prerequisite is necessary.
Master integration remains separately user-controlled.
