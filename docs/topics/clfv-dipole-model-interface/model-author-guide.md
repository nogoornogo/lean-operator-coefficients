# Registering A Dipole Model

Import `Physics.StandardModel.Operators.DipoleModelInterface`; use
`Physics.StandardModel.Operators.DipoleMatrixInterface` for coordinate matrices.
The [compiled examples](../../../Physics/StandardModel/Operators/DipoleModelExamples.lean)
exercise each route below. They are algebraic samples, not physical matching.

## What The Author Supplies

Supply residual representations a on A and b on B (B finite-dimensional), an
input type X, the admissible subset of X, a supplied incoming flavor vector
and outgoing flavor covector, and a coefficient-generation law. Generation
need not be linear; X need not be a vector space.

The targeted full coefficients are the two independently classified chiral
SM dipole sectors, not two unconstrained complex numbers. A physical matching
calculation, normalization/convention conversion, and identification of the
flavor labels belong to the model author. They are not inferred by this API.

## Registration Routes

1. **Residual maps already known:** `DipoleModelInterface.ofResidual` takes
   the admissible domain, flavor identifications and the two residual
   intertwiners at every input. It reconstructs the full coefficient pair.
2. **Coupling structure known:** `DipoleModelInterface.ofCouplings` takes
   existing `DipoleCouplingModel.Couplings`, a parameter domain and maps from
   that same parameter type into incoming and outgoing coupling spaces. These
   maps may be nonlinear or correlated. The coefficient correspondence is derived.
3. **Existing full coefficient calculation:** create a residual registration
   by either route, then call `r.withCoefficients F hF`. The author supplies
   exactly one correspondence proof on admissible inputs:

```lean
hF : ∀ x ∈ r.admissible,
  (DipoleSMCoefficient.equiv a b) (F x) = r.residual x
```

Alternatively construct `Registered` directly with fields `admissible`, `mu`,
`electron`, `coefficients`, `residual`, `correspondence`. Supplying an equality
as a hypothesis proves the implications using it, not the matching equality
itself. Literature-based matching inputs must be documented with conventions
and application conditions; they cannot become custom Lean axioms.

## Apply Conditions

For a registered model r:

```lean
r.observe x              -- selected B and W pair
r.NonzeroInput x         -- admissible x AND selected pair is nonzero
r.selected x hx          -- evaluate via residual maps; requires admissibility
r.nonzero_iff x          -- exact admissibility and selected-channel criterion
r.nonzero_of_channel x hx h
r.forbidden_of_distinct_weights g alpha beta hmu he hne
```

`withCoefficients` preserves `NonzeroInput` on the registered domain by
`nonzero_withCoefficients_iff`. No independent Wilson-coefficient adjustment
or surjectivity of the physical generation map is assumed.

## Correlated And Restricted Parameters

`r.restrict s` retains only inputs in both the registered domain and s.
`r.pullback f` changes parameters through any f : Y -> X; its admissible
domain is the preimage of the registered domain. The exact relations are:

```text
restricted NonzeroInput x iff r.NonzeroInput x and x belongs to s
pullback NonzeroInput y iff r.NonzeroInput (f y)
exists a pullback nonzero input iff r has a nonzero input in range f
```

These statements intentionally do not transfer nonzero existence to an
unreachable or correlated domain. Conjugate/adjoint relations can be encoded
in a supplied parameter map; this interface does not compute adjoints or
prove that such a parameterization has independent coordinates.

For polynomial residual dependence, supply `PolynomialCertificate`: an
independent product of infinite coordinate sets equal to the actual admissible
domain, fixed residual paths, polynomial weights and their expansion equality
on that domain. The weights can share coordinates, so correlated polynomial
couplings and same-monomial cancellations are supported.

```lean
c.exists_nonzero_iff  -- exists admissible nonzero input iff some c.grouped d != 0
c.no_nonzero_iff      -- no admissible nonzero inputs iff every c.grouped d = 0
```

`grouped` adds all paths at each monomial before testing either selected
channel. A correlated *image* need not be an independent-coordinate product;
parameterize it by actual free coordinates and certify the polynomial law
there instead. Ordinary complex polynomial hypotheses do not automatically
cover conjugates, rational functions or logarithms in the supplied coordinates.

## Automatic Polynomial Coupling Certificates

Import `Physics.StandardModel.Operators.DipolePolynomialAutomation`. For a
compositional coupling model, supply finite incoming/outgoing bases and
polynomial coordinate families p and q in the same free parameters. Then use:

```lean
DipolePolynomialAutomation.register a b m model bu bv p q s mu electron
DipolePolynomialAutomation.certificate a b m model bu bv p q s mu electron hs
```

Here s supplies the allowed set for each free coordinate, and hs proves
each set infinite. Registration itself does not require hs. The constructors
evaluate p and q into coupling vectors, derive basis paths and product
weights p_j*q_k, and prove the expansion. Shared parameters and equal
coordinate polynomials are supported without assuming independent couplings.
No manual path list or residual expansion proof is needed.

The returned certificate uses the existing `exists_nonzero_iff`,
`no_nonzero_iff` and `grouped` API. To attach a previously computed full
coefficient law, use `c.withCoefficients F hF`; it transports the certificate
to the corresponding `r.withCoefficients F hF` while retaining the author's
matching/correspondence obligation.

This is certificate-construction automation, not arbitrary expression
recognition or automatic nonzero decision. See the
[compiled automation examples](../../../Physics/StandardModel/Operators/DipolePolynomialAutomationExamples.lean)
and [scope/results](../clfv-dipole-polynomial-automation/results.md).

## Matrix Route

`DipoleMatrixInterface.register` accepts B/W matrices with rows indexed by
the output flavors and columns by the input flavors. The author proves that
each matrix commutes with the respective residual actions (`mulVec` form).
The chosen incoming vector is the mu coordinate basis vector; the outgoing
covector selects the e coordinate. `selected_entry` proves:

```text
registered observe x = (matrixB(x)[e,mu], matrixW(x)[e,mu])
```

Equivariance is required at all inputs of this matrix constructor; use the
subtype of valid inputs if it is known only on a physical parameter domain.
The matrix registration can also receive an existing full coefficient map
through `withCoefficients`. Thus matrix authors need not manually construct
the intertwining maps or redo the coefficient classification.

## What Nonzero Means

The monitored quantity is a pair of chiral B/W flavor components. It is not
a matched photon amplitude or decay rate. B/W electromagnetic combinations
can cancel, and flavor identifications are supplied, not derived mass states.
Matching/RGE, rates and experimental comparison remain external responsibilities.
