# Pati–Salam: Gauge Permission Versus Accidental Baryon Number

## Fixed Variant And Result

Fix the minimal setup of [2211.02054v2](https://arxiv.org/abs/2211.02054v2),
Section II Eqs.(1),(2),(5),(10): one generation of fL=(4,2,1), fR=(4,1,2),
chi=(4,1,2), Phi=(1,2,2) and a singlet xi. The neutral chi component has a
nonzero VEV; Phi has zero VEV at the stage considered. No other matter/scalar
variant is covered. This is an algebraic comparison of supplied SM dictionary
and actions, not a complete phenomenologically fitted PS model.

The gauge-only SM light dictionary admits the common-copy mechanism (H=1).
The optional accidental baryon action instead forbids qque and fails the common
source condition. That action is not required by gauge invariance of the higher
operators in this variant. Thus absence of renormalizable gauge-mediated decay
is not a counterexample to a nonzero invariant-coefficient theorem.

## Species, Mass And Common Copies

From Eq.(1), fL supplies Q,L and fR supplies uR,dR,eR,nuR; the latter become
uc,dc,ec,nuc in an all-left mass dictionary. The charged SM hypercharges 6Y
are (1,-4,6,2,-3). Scalar and neutral fields add no conjugate partner for Q,uc,ec.
In the supplied complete unbroken-SM dictionary their high-scale symmetric mass
blocks vanish by representation mismatch. The neutral nuR/xi block may have
Dirac and Majorana entries independently and does not change those light ranges.
The exact script checks Eq.(12)'s neutral matrix with the EW entry set to zero.

Under the gauge-only dictionary the remaining action is SM, with H=1. All
charged copies are the same trivial residual representation. For one generation
S=ℂ and T=0 give three injective species maps and zero copy masses. For replicated
unchanged generations the same structural argument uses S=ℂ^n. No semisimplicity
or dimension obstruction arises. A full PS branching/stabilizer and actual-field
adapter have not been constructed in Lean; these remain supplied model inputs.

`gauge_only_qque_allowed` gives a nonzero element of the physical one-generation
qque family on the specified trivial residual dictionary, including SM/Lorentz
and exterior statistics. It asserts permission, not a PS UV matching coefficient.

## Accidental B Is Optional

Eqs.(17),(18) define a global J with B=(J+T)/4, T=B-L. On quark/lepton components
J=1 and T=(1/3,-1), giving the usual baryon charges. The neutral chi VEV has B=0.
If one chooses this accidental U(1)_B as an exact H, Q and uc have opposite
nonzero weights and ec has zero weight, so a common nonzero source fails; physical
qque has delta B=1. Meanwhile qque is B-L-neutral. B-L neutrality is only a
charge control, not proof of invariance under a hypothetical extra residual.

Section III Eq.(19) supplies the gauge-invariant chi² f_X² epsilon contraction,
with net J=4. The script checks a nonzero polynomial component: contracting
SU(4) and the two SU(2) epsilons gives coefficient4 for two distinct fermion
components and two commuting scalar components, one in the neutral VEV slot.
This confirms that the suggested contraction is not zero just because the two
scalars coincide. It breaks the optional J/B symmetry. Gauge invariance here
uses determinant-one epsilon tensors; no complete operator basis is certified.

The paper's induced LEFT operators in Eqs.(22),(23) are udd-neutrino channels,
not a UV matching proof for qque. This initial comparison stopped before
matching/rates. The later [conditional component certificate](generated-coefficient.md)
checks symbolic generation, with an explicit source-normalization boundary and
no rates.
A claim of exact B protection would need an additional assumption excluding
such higher operators; it is not supplied by the gauge group alone.

## Stop And Evidence

The gauge-only/accidental-action comparison and finite polynomial check close
the bounded evaluation. Stop before new PS representation foundations, global
stabilizer formalization, all-operator classification or phenomenology.

See [exact checks](../../../tools/proton-protection-model-checks/README.md),
[Lean controls](../../../GUT/Common/ProtonProtection/ModelControls.lean),
[verification](../../topics/proton-protection-model-checks/verification.md), and
[the journal paper](https://doi.org/10.1103/PhysRevD.107.035019).

## Species-Dependent Theorem Recheck

See the [independent-species recheck](species-surplus-check.md) for the new Hom
surplus criterion, original-mass compatibility and remaining UV inputs.
