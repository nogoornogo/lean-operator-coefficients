# PS To SM Representation Admission

The covering-group representation bridge is proved. It identifies genuine PS
fermion tensor representations with all SM components through mutually inverse
equivariant linear maps, and connects chi/Phi coordinates to the earlier
component conventions. It does not prove the complete invariant-action or
paper-normalization comparison. See the [plan](representation-admission-plan.md)
and [verification](representation-admission-verification.md).

## Groups And Conventions

[StandardModelEmbedding](../../../GUT/PatiSalam/Embeddings/StandardModel.lean)
constructs a group homomorphism from the existing covering product
SU(3)×SU(2)L×U(1) into SU(4)×SU(2)L×SU(2)R:

- SU(4): diag(z A,z⁻³), reindexed into Fin 4 with colors first.
- SU(2)L: B.
- SU(2)R: diag(z³,z⁻³).

Both nontrivial blocks are proved unitary with determinant one; multiplication
is proved before bundling the homomorphism. This is a homomorphism of covering
products, not a claimed injective map of that SM cover. Its kernel, global
center quotient, full chi stabilizer and topological quotient are not identified.
The exponents are integral hypercharges 6Y.

The pinned source is [Dutka–Gargalionis, 2211.02054v2](https://arxiv.org/html/2211.02054v2),
Sec.II Eqs.(1),(2),(5)–(7), with
[PDF](https://arxiv.org/pdf/2211.02054v2) and
[publication](https://doi.org/10.1103/PhysRevD.107.035019).
These expressions motivate the dictionary; the homomorphism and intertwiners
are proved algebraically rather than accepted as literature premises.

## Fermion And Chi Components

[ComponentRepresentations](../../../GUT/PatiSalam/Embeddings/ComponentRepresentations.lean)
constructs the PS fundamental actions and the genuine tensor representations
fL=(4,2,1), fR=(4,1,2). Their restriction along the homomorphism has the following
complete decomposition, using the existing StandardSMGaugeTensor representations:

| PS space | SM component | Color, weak, 6Y |
| --- | --- | --- |
| fL | Q | 3,2,1 |
| fL | L | 1,2,-3 |
| fR and chi | uR or chiU | 3,1,4 |
| fR and chi | dR or chiD | 3,1,-2 |
| fR and chi | nuR or chi0 | 1,1,0 |
| fR and chi | eR or chiMinus | 1,1,-6 |

Each component inclusion is equivariant for every SM covering-group element.
The full joins and splits are linear equivalences; their bundled intertwiners
are mutually inverse. Thus the projections are also equivariant, and no extra
component is discarded. These are right-handed uR,dR,eR representations;
identifying conjugate all-left-handed fields still requires the stated
conjugation convention. Lorentz/spin factors are spectators here.

A linear equivalence transports the tensor representation to exactly the
Fin 4→Fin 2→complex arrays used by earlier contractions. The neutral inclusion
is proved equal to ComponentAdmission.neutralVEV, and the selected colored
chiD inclusion is proved equal to the Pi.single array used in the colored
vertex. The neutral chi VEV is fixed by every embedded SM group element.
This proves inclusion of the image in its stabilizer, not equality with the
entire PS stabilizer. No scalar potential or vacuum-selection result follows.

## Phi Columns

[PhiRepresentation](../../../GUT/PatiSalam/Embeddings/PhiRepresentation.lean)
uses an explicit dual right-index convention: Phi=Hom(TwoR,TwoL), with action
Phi↦left(g)∘Phi∘right(g⁻¹). This avoids silently identifying a right index with
its dual. No separate SU(2) self-duality adapter is claimed.

Column evaluation at the two right basis vectors gives a linear equivalence
with two weak doublets of 6Y=-3,+3. Both directions are bundled intertwiners.
Matrix-column evaluation is proved to agree with this map, including the
previous diagonal Phi vacuum. Unlike neutral chi, an electroweak Phi vacuum
is not asserted fixed by the full SM group.

## Closed And Remaining Obligations

The previous missing covering-group branching/component-intertwining interface
is now constructed, including chi VEV compatibility and explicit Phi columns.
Earlier result files describe their own checkpoints; this result supersedes
only their statement that these representation maps were absent.

The complete PS-invariant Yukawa and UV epsilon actions still need to be
identified with the prior typed coefficients through these maps. In particular,
branching alone is not a proof of full UV-operator invariance, signed fermionic
transport, or equality of the complete source action. Existing selected finite
contractions remain proved in their specified conventions. The earlier sqrt(2)
comparison is not repaired or independently validated by this bridge.
No multi-generation nonzero matching, finite-mu spectrum, rate or paper-wide
correctness theorem is added. The user-requested representation bridge is the
completed endpoint; master integration remains separately authorized.
