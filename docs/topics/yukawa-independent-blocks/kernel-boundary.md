# Concrete UV Kernel Diagnosis And Resolution

Status: resolved without changing the target equality, physical assumptions,
projector definitions, toolchain or heartbeat limits. The original direct
specialization below is a failed route, not the accepted proof.

## Isolated Failure

Partial applications of `transformed_bilinear` were kernel-checked one argument
at a time. The actual forms B and D, branching map e, projectors p and q,
`original_pullback` and `branch_projection` all passed. Supplying
`branch_anti` as the next argument caused the deterministic kernel timeout.
Elaborated-type comparison exposed the conversion from representation-map
coercions to linear-map coercions in that concrete equality.

An explicit coercion lemma also timed out. Reconstructing q first with
`x - p x`, then with its simplified coordinate formula, did not fix that
application; both implementation changes were reverted. This isolates the
problematic conversion path but does not establish a low-level kernel bug
or a complete account of its reduction cost.

The following extracted direct specialization failed with the pinned toolchain.
It is retained as diagnostic documentation, not imported as a theorem.

```lean
import GUT.SU6.Yukawa.IndependentCouplings

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6IndependentCouplings
noncomputable section
open StandardSMUVFields
attribute [local irreducible] ConcreteWeylBenchmark.matter
variable (H : Type*) [CommGroup H]

def failed_direct_specialization (a b : ℂ) :=
  transformed_bilinear H
    (StandardSMUVMass.mass H).form
    (SU6TwoBlockSpectrum.massCertificate H a b).mass.form
    (withResidualEquiv H).toLinearEquiv.toLinearMap
    exteriorProjection.toLinearMap antiProjection.toLinearMap
    (original_pullback H) (branch_projection H) (branch_anti H) a b
    (SU6TwoBlockSpectrum.massCertificate H a b).form_eq

end
end GUT.SU6IndependentCouplings
```

## Accepted Proof

The proved endpoint is
`mass H a b = SU6TwoBlockSpectrum.mass H a b`, where the left side is
the actual Yukawa evaluation at the existing fixed vacuum.

`transformed_complement` derives the complementary branching equation while
the carrier and linear maps are still abstract. Instead of receiving
`e (q x) = e x - fieldsProjection (e x)`, it receives the smaller equality
`q x = x - p x`. Linearity of e and the already supplied projection identity
then prove the former equation with `rw [hq, map_sub, hp]`.

The concrete smaller equality is proved by `anti_eq_sub`, not assumed.
The resulting `projected_mass_form` is kernel-checked, and
`ProjectedYukawa.generated_mass_eq_from_form` with `baseYukawa_vacuum` yields
`mass_eq`. The full radical equivalence, all four dimension strata and the
injectivity of the two-coefficient coupling family now follow and are included
in the strict transitive axiom audit. The complete model module built in
approximately six seconds in the focused check; no timeout override was needed.

Earlier attempts included pointwise/form-level transport and temporary local
heartbeat increases; none yielded an accepted direct specialization, and all
diagnostic overrides were removed. The resumed pass used ordinary limits.

There is no `sorry`, new axiom, weakened audit or extra physical premise.
No scalar potential, new Higgs choice or external literature was introduced.
See the topic README for focused/full verification and remaining scope limits.
