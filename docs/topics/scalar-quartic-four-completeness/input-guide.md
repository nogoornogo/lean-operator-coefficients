# Using The Complete Order-Four Coefficient Input

Import `Physics.FieldTheory.Jets.ScalarQuarticFourCompleteness`. The namespace
`GUT.ScalarQuarticFourTensors` supplies `V` (the full grade 4,4), `P` (the
existing free scalar input) and `selected := P.select V stable`. Selection
uses the preimage of all unbounded EOM/IBP relations.

In `GUT.ScalarQuarticFourCompleteness`:

- `normalized : selected.Coefficient` is the admitted coefficient with
  K-squared value 1.
- `equivalence : selected.Coefficient ≃ₗ[ℂ] ℂ` extracts that value.
- `reconstruction F` identifies every F with its value times `normalized`.
- `arbitrary_value c` and `coefficient_dimension` give arbitrary complex
  values and dimension one.

This is an added certificate on the existing selected input, with no new
caller hypothesis or change to the nonderivative interface. For example:

```lean
import Physics.FieldTheory.Jets.ScalarQuarticFourCompleteness

open GUT.ScalarQuarticFourTensors GUT.ScalarQuarticFourCompleteness

example (F : selected.Coefficient) : (equivalence F) • normalized = F :=
  reconstruction F

example (c : ℂ) :
    (c • normalized).val GUT.ScalarQuarticFourUpper.generator = c :=
  arbitrary_value c
```

Whole-source consumers first use `P.restrict V stable`. The
[checked consumers](../../../Physics/FieldTheory/Jets/ScalarQuarticFourChecks.lean)
prove its extracted coordinate is the original coefficient's K-squared
value, and selected quotient extraction agrees with direct evaluation.
The raw linear `functional` annihilates the entire relation module; its
invariance theorem is scoped to V. Use `normalized` for this admitted input.

The complete coefficient line coexists with quotient classes outside the
K-squared line. The checked anisotropic probe demonstrates that distinction.
The certificate applies to the free single-scalar 4,4 input; other degrees,
interactions and mixed-statistics sources keep their own input contracts.

For paper-normalized inputs, import
`Physics.FieldTheory.Jets.ScalarQuarticLiteratureChecks`. Its namespace
`GUT.ScalarQuarticLiteratureChecks` supplies `first`, `second`, `third` and
`chosen` as elements of the same complete V. `chosenEquivalence` extracts
the chosen density's value, and its inverse sends z to `(2/3*z) • normalized`.
`admitted_triple` gives the necessary and sufficient compatibility of the
three density values, including uniqueness. The
[literature recheck](literature-validation.md) fixes the dictionary and scope.
