# Conditions For A Protecting SU(6) Input

The existing protecting lepton-parity SM input cannot be lifted to the
standard-embedding, commuting-cyclic, pure-generation SU(6) class below.
The [new structural test](../../../GUT/SU6/SelectionRules/Models/CyclicProtectionFeasibility.lean)
proves this for arbitrary positive cyclic order and generation multiplicity,
without a bound on UV representations or copies. No protecting SU(6) model
is constructed by this test, and no unrestricted SU(6) impossibility follows.

## Exact Class And Obstruction

Supply an actual finite-dimensional complex unitary representation of
SU(6) times a commuting cyclic group, the standard physical restriction
with torus integers (-2,3), and any invariant symmetric complex-bilinear
mass on that restriction. The mass need not be invariant under all SU(6).
Require a positive pure-generation chiral dual index of its actual radical,
with arbitrary singlet index. This is weaker than an exact light spectrum;
extra vectorlike pairs do not evade the index condition.

With all-left species ordered Q, uc, dc, L, ec, neutral ordinary Yukawa
channels give the generation-universal dictionary

$$
(q,-q-h,-q+h,l,-l+h),
$$

where h is the Higgs charge. The actual SU(6) index theorem forces the
Q, uc and ec characters to agree. Faithfulness of cyclic characters gives

$$
q=-q-h,\qquad q=-l+h,\qquad\text{hence}\quad 3q+l=0.
$$

Changing the Higgs charge alone therefore does not repair this index gate.
`GUT.SU6ProtectionFeasibility.target_forces_yukawa_neutral` supplies this
constraint; `no_target_of_light_forbidden` consumes the actual infrared
prohibition predicate in the neutral-Higgs specialization.
At h=0 the existing actual three-generation four-family coefficient theorem
identifies `3q+l=0` with allowance of a bounded dimension-six B1 sector.
Its prohibition condition `3q+l≠0` contradicts the proposed UV target.
Here B1 means absolute baryon-number change one. The charged-Higgs statement
is an index constraint, not a new coefficient-space classification.

The associated infrared coefficient is a genuine statistical/gauge/Lorentz
coefficient. This does not manufacture an equivariant identification with
an arbitrary UV radical. Such a light-field dictionary remains a separate
model-admission requirement.

## Concrete Checks

| Input | Result and boundary |
| --- | --- |
| Z2 lepton parity: q=0, l=1, h=0 | Existing actual three-generation SM radical, invariant spectator mass, nonzero charged-fermion Yukawa coefficients and all-degree derivative-free B1 prohibition are retained. The proposed commuting standard-chain SU(6) target is impossible. Nonzero Yukawa coefficients do not certify full-rank physical mass matrices. |
| Neutral q=l=0 | The actual bounded infrared B1 input is allowed. The test does not label every input protecting or every SU(6) spectrum impossible; no UV realization is inferred from this control. |
| Unequal S3 actions: Q permutation, u trivial, e sign | Actual qque coefficients vanish, but there is no common uniform flavor dictionary, and the stated neutral-Higgs Q-to-u maps cannot be injective. Other B1 sectors and a UV radical remain unverified. |
| Q permutation, u=e sign | Actual qque is allowed despite no shared Q/sign irreducible. This prevents using constituent mismatch as a prohibition test. |

The cyclic phases agree with the existing scalar actions through
`cyclicLabel_scalar_action`. The simultaneous concrete checks are in
[ProtectionFeasibilityControls](../../../GUT/SU6/SelectionRules/Models/ProtectionFeasibilityControls.lean).

## What A New Candidate Must Supply

A candidate must escape at least one hypothesis of the excluded class.
This is a disjunction; no single escape is universally necessary or sufficient.
Adding larger multiplets, changing copy numbers, retuning an invariant mass
or adding only vectorlike light pairs is insufficient within that class.

| Construction choice | Required certificate before calling it a protecting model |
| --- | --- |
| Genuine noncommuting residual action | Its group law, UV gauge covariance, SM-image normalization, fixed supplied vacuum and mass invariance; an SM gauge factor invisible to invariant coefficients is not a new protecting action. |
| Different light flavor or chiral content | Actual SM/residual-equivariant radical maps, all additional light states and their statistics; any declared full-rank Yukawa requirement must also hold. |
| Different SM embedding | The actual group homomorphism, hypercharge normalization, branching and mass-radical dictionary; relabeling a torus charge is insufficient. |
| Different zero-mode mechanism | An explicit mode-selection map and its symmetry and light-spectrum proof, rather than substituting a selected subspace for a mass radical. |

On the resulting **same** fields, actions and relations, prove coefficient
vanishing on the whole requested B1 domain. A qque-only result is insufficient.
For derivatives/EOM/IBP use the full stable relation module and exact selected
preimage. The Lagrangian input can derive Euler covariance from total-density
invariance for its admitted actions; it does not discover the UV realization.
An old unquotiented coefficient is not silently claimed to survive arbitrary
interacting EOM, nor does EOM redundancy alone establish a protecting symmetry.

## Published Construction With A Different Boundary

[Angelescu et al., arXiv:2104.07366v2](https://arxiv.org/html/2104.07366v2),
Sec. II and Appendix C, give a concrete five-dimensional SU(6) construction
with bulk 20,15,6,1 matter and boundary-selected chiral modes. The authors
claim perturbative baryon protection and explicitly note an anomaly.
The [boundary algebraic construction](boundary-model.md) now verifies the
unmixed chiral projectors, actual exterior-field maps, residual baryon action,
internal boundary contractions and SM/Higgs coefficient prohibition. Analytic
mixed-mode admission, anomaly cancellation and full-model claims remain
separate. This is a different construction class from the finite-dimensional
symmetric-mass input above.

The [source register](../../topics/su6-protection-feasibility/references.md)
records inspected locations and the [boundary verification](../../topics/su6-protection-feasibility/boundary-verification.md)
separates proved tensor identities from the paper's analytic and quantum claims.

## Result And Evidence

The concrete infrared model is checked and its proposed UV lift is refuted
in the admitted class. The remaining candidate conditions are explicit;
their realizability is not proved. The
[owning topic](../../topics/su6-protection-feasibility/README.md) and
[verification](../../topics/su6-protection-feasibility/verification.md)
record the strict audits and build checks. Quantum exactness, anomaly
cancellation, realistic masses, matching and rates remain separate inputs.
