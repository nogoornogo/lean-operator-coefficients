# Fixed S3 sample: result and boundary

## Input

The group is S3 and every fermion flavor carrier is Fin 3 → C. In physical
right-handed conventions Q,uR,dR carry the permutation representation and
L,eR carry three copies of the sign character. The Higgs weak doublet is
residual-neutral. Gauge, spin and residual actions use the existing independent
product convention. The [source](../../../Physics/StandardModel/Operators/S3YukawaCompatibleQque.lean)
records this dictionary with `Species`, `flavor` and `higgsFlavor`.

## Certificates

`quark_actions_noncommute` proves noncommutativity on the actual quark carrier,
rather than just noncommutativity of abstract S3. `preserves_sm` proves that
each species flavor action commutes with any independent SM gauge action,
including its actual SM representation. This is a product-action certificate;
it does not construct a new gauge normalizer or UV lift.

`flavor_map_gates` supplies bijective invariant maps Q→uR, Q→dR and L→eR
from identity intertwiners. Thus the specific noninjective/zero flavor-map
obstructions of the [previous unequal samples](../sm-support-and-lfv-decomposition/sm-preserving-sample-results.md)
are absent. Interpreting these maps as complete physical Yukawa tensors would
require the additional gauge/Higgs/spin correspondence. No such matching,
realistic mass eigenvalues or mixing is asserted here.

For flavor vectors x,y,z,r assigned to Q,Q,uR,eR, the coefficient is

    det(ones, x*y, z) * sum(r),

where x*y is coordinatewise multiplication and the determinant uses columns.
The source explicitly builds the linear map on (V⊗V)⊗(V⊗V), proves its
formula and checks invariance through the existing six S3 normal forms.
The determinant and electron sign factors cancel. Coordinatewise x*y is
symmetric in the two Q inputs. The value at (e0,e0,e1,e0) is exactly 1.

`allowed_dictionary` transports this nonzero symmetric residual coefficient
through the existing physical qque exterior coefficient equivalence. Therefore
the actual statistics-constrained selected qque sector is allowed for this
same dictionary. There is no extra semisimplicity, character-table or external
literature premise. The strict audit is
[AuditS3YukawaCompatibleQque](../../../Physics/StandardModel/Operators/Audit/AuditS3YukawaCompatibleQque.lean).

## Meaning and stopping decision

This is a nontrivial residual-action example passing the specified flavor-map
gates while allowing qque. It supplies no symmetry prohibition of this sector.
An allowed coefficient is not a generated interaction or a decay-rate result.
The result does not classify all B1 sectors or all residual actions, and does
not assert anomalies, a full Yukawa certificate, SU6/UV realization, mass/VEV
selection, matching or a bridge to the ten-species signed SM/Higgs dictionary.
No such further input is needed to close this selected-sector endpoint.

The original coefficient route succeeded; the orbit-sum fallback was unused.
The successful stop is verification and a topic commit, pending any separately
authorized integration. The general procedure and other applications remain
separate follow-ups.

## Supplementary exact check

Run `python3 tools/s3-yukawa-compatible-qque/check_sample.py` from the repository
root. The script uses only Python's standard library and exact integer
arithmetic. It checks all 6×3⁴=486 group/tensor-basis cases, all 3⁴=81 Q
exchange cases, and the value 1 witness. A negative control removes the electron
sign and gives -1 under a transposition, detecting a lost sign convention.
Multilinearity explains the finite basis coverage. The script is supplementary
and is never a theorem premise; Lean independently proves the coefficient and
its physical exterior transport. Disposable build logs live outside the repository.

See [verification](verification.md) for acceptance commands and outcomes.
