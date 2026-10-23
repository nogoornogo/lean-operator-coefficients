# Generated Gaugeless Higgs Input

[`Physics.HiggsStandardInput.input`](../../../../../Physics/FieldTheory/Jets/Higgs/Inputs/HiggsStandardInput.lean)
accepts complex potential parameters a,b. It generates the common derivative
input for the two-component kinetic density minus a*rho minus b*rho squared/2.
The caller supplies neither component Euler equations nor covariance proofs.

The actual ordinary jets carry the paired fundamental/dual Higgs representation
on the covering SU(3) × SU(2) × U(1) gauge group and the existing SL(2,C)
Lorentz direction action. Integral hypercharge is 6Y=3 for H and the opposite
for its dual; color acts trivially. The action is global. Covariant derivatives,
gauge connections and Yukawa sources are not supplied by this entry.

The [Math generator](../../../../../Math/RepresentationTheory/Lagrangian/HiggsLagrangianInput.lean)
proves density evaluation and all Euler components: variation of each label
generates the negative direct equation for the opposite label. Full generated
and direct differential ideals and EOM/IBP relation modules coincide. Their
coefficient maps are inverse and preserve evaluation. The five-representative
C3 relation therefore holds for every admitted coefficient of the generated
physical-group input.

The [field dictionary](../../../../../Physics/FieldTheory/Jets/Higgs/Inputs/HiggsFieldDictionary.lean)
proves the actual dual/conjugate group transport. Conjugate component values
form an explicit semilinear real-form condition preserved by the internal
action. They are not imposed as a complex-linear equation identifying the
independent polynomial generators. Arbitrary complex a,b are algebraic
parameters; Hermiticity for nonreal couplings and analytic actions are not
asserted. There is no complete invariant-basis or Warsaw-basis theorem here.

The [topic](../../../../topics/derivative-literature-foundations/README.md),
[phase record](../../../../topics/derivative-literature-foundations/progress.md)
and [usage](../../../../topics/derivative-literature-foundations/input-guide.md)
own the implementation scope and verification evidence.
