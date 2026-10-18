# Split SU(5): Two Different Admission Questions

## Result And Inputs

This model does not justify the blanket claim that every stable-proton model
fails the common-copy theorem. On the gauge-only broken-phase SM dictionary
(H=1), its light species can satisfy the inlet. Under an additional exact light
lepton parity, the common source fails and qque is forbidden. The latter is a
conditional effective-field action, not automatically a symmetry of the full
UV mass/Lagrangian.

Inputs are [1706.08535v2](https://arxiv.org/abs/1706.08535v2), Eq.(1) for SM
branching, Eqs.(6),(7),(10),(15),(16) for mass splitting, Eq.(4) for couplings
and Eq.(22) for parity. One chiral generation, two vector-like 40/50 copies,
and scalars 24,45,75 are fixed. Work before electroweak breaking. Branching
and the UV mass formulas are supplied literature data, not newly proved here.

| Left species | Full copies and partners | Selected light origin |
| --- | --- | --- |
| Q | 10,40_1,40_2; two conjugate partners | two 40 copies |
| uc | 10,40_1,40_2; two conjugate partners | two 40 copies |
| ec | one 10; no matching conjugate | 10 |
| dc | 5c,50c_1,50c_2; two conjugate partners | two 50c copies |
| L | one 5c; no matching conjugate | 5c |

Hypercharges are the usual all-left (1,-4,6,2,-3) in units6Y. Right-handed
uR/eR are duals of uc/ec when forming physical qque.

## Exact Mass-Kernel Analysis

For Q,uc,dc write the supplied rectangular block as M=[a|C], with two rows,
three columns and C square2. A nonzero pure 40/50 null vector exists iff C is
singular. If rank M=2, singularity implies rank C=1 and the unique light line
lies entirely in the two exotic copies. If C is invertible, the light line is
spanned by (1,-C⁻¹a), so it generally contains the 10/5c component. Singularity
alone does not establish uniqueness or the asserted heavy spectrum.

The exact script checks pure lines with Q kernel (0,0,1), uc kernel (0,1,0),
a mixed control and a rank-deficient control. These are rectangular-block
controls, not an asserted simultaneous point in the full UV coupling space.
The differing Q and uc directions do not obstruct a common abstract source:
the theorem permits different species embeddings and different mass maps.

For H=1, each charged light copy is trivial. With the supplied complete SM
block dictionary, rank-nullity gives a nonzero Q and uc kernel and ec survives;
one may take S=ℂ, T=0 and embed into independently derived light lines. The mass
squares then hold with zero copy maps. This is a conditional algebraic feasibility
argument, not a new Lean construction of the full 40/50 carrier or its arbitrary
mass classification. The existing one-copy gauge-only physical qque permission
certificate applies to the derived species dictionary. Its nonzero coefficient
space is compatible with absence of a generated UV coupling.

## Parity Is A Different Question

On selected light fields Eq.(22) gives (Q,uc,ec) signs (+,+,-). Any common
nonzero S would have to be both even and odd. The scalar-embedding lemma rules
this out. `light_parity_selection` proves all four one-generation BNV families
vanish under this supplied light action.

But the 10/5c-to-vector-like mixing terms proportional to lambda3, lambda5,
lambda8 are parity-odd; the script checks their signs and a full mass block's
non-invariance. Therefore this parity cannot simply be fed into a Model of the
original invariant symmetric mass. Eq.(4) also sets another allowed Yukawa
coupling to zero. Section V's nondynamical-condensate/nonlinear-breaking
prescription and Footnote 1's extra EW-mixing condition are further boundaries.
Neither the high-scale determinant conditions alone nor the light parity
certificate proves exact all-scale proton stability.

## Stop And Evidence

Two allowed routes have been evaluated: gauge-only light dictionary and
conditional light parity. Stop at this feasibility decision before full SU(5)
40/50 branching, a UV parameter certificate, post-EW mass analysis or nonlinear
quantum matching. No failed necessary condition is claimed for H=1.

See [exact checks](../../../tools/proton-protection-model-checks/README.md),
[Lean controls](../../../GUT/Common/ProtonProtection/ModelControls.lean),
[verification](../../topics/proton-protection-model-checks/verification.md), and
[the journal paper](https://doi.org/10.1103/PhysRevLett.119.241801).

## Species-Dependent Theorem Recheck

See the [independent-species recheck](species-surplus-check.md) for the new Hom
surplus criterion, original-mass compatibility and remaining UV inputs.
