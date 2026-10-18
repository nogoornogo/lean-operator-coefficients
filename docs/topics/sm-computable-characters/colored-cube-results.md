# Middle colored exterior cube: proved decomposition

Continuation from `checkpoint 01` on `proof/sm-computable-characters`, targeting
`master` without merge or push authorization. The [frozen plan](colored-cube-plan.md)
is complete for the U/D color/spin cores, including their conjugates.
The original complete mixed q/l support classification is **still open**.
See [verification](colored-cube-verification.md) and the updated
[remaining colored obligations](colored-core-boundary.md).

## Statement and actual consumers

`SU3SpinExteriorCube.cubeEquiv` proves the actual SU3 × SU2 equivalence

```text
Lambda^3(color tensor spin)
  = Sym^3(spin) direct-sum (trace-free End(color) tensor spin).
```

`SU3ConjugateSpinExteriorCube.cubeEquiv` proves the same decomposition
for dual defining color. Its middle branch is the actual conjugation action
on trace-free endomorphisms of the dual color module. No identification of
color with dual color, or unproved self-duality/irreducibility of an adjoint,
is used.

`SMColoredCubeBranching.positiveCube` and `negativeCube` transport these
complete decompositions to the actual signed U/D core species `1,2,6,7`.
The full retained semisimple group is SU3 × SU2weak × SU2left × SU2right;
the positive cores use the right-spin projection and the conjugate cores
the left-spin projection. No charge phase is inferred or discarded: these
are semisimple core decompositions, not new all-Higgs permission iff claims.
Together with the previous square/complementary identities, they close the
single-generation colored-doublet exterior branches through capacity.
The Q core has two independent doublet factors and remains a separate case.

## Symbolic construction

`ExteriorCubeHook` constructs multiplication W from V tensor Lambda^2(V)
to Lambda^3(V), and the three-slot coproduct delta. It proves W delta=3 id
on arbitrary vectors. The hook is the actual kernel of W; its projection
is id-(1/3) delta W. `ExteriorCubeHookRepresentation.split` retains any
group action and gives a complete split without dimension or irreducibility
assumptions.

`ExteriorCubeDoublet` uses the invariant alternating spin pairing to define
a contraction G from the exterior cube, and the invariant spin bivector to
define an insertion J. Universal alternating identities prove

```text
G J = 9 (hook-inclusion hook-projection tensor spin-identity).
```

Consequently the hook tensor doublet has an actual split embedding, with
left inverse `(1/9) (hook-projection tensor identity) G`. G kills the
other top-column map from Sym^3(spin). Polarization and the proved
injectivity of that column map then show that the two images are independent.
`ExteriorCubeDoubletNaturality` proves that G and J respect color and spin
actions, using determinant one for the spin bivector.

For a three-dimensional color module, `ExteriorCubeDoubletSplit` proves
that the combined injection is surjective. This uses the standard exterior,
symmetric-power and tensor dimension formulas, and the already proved hook
splitting. The dimensions here count functor bases of the small core;
no content coefficient matrix, evaluated multiplicity or numerical rank
certificate is supplied. No large exterior basis is expanded. The constants
3 and 9 above normalize universal maps; they are not multiplicities.

`SU3ColorHook` and `SU3DualColorHook` identify the hook with actual trace-free
endomorphisms. Complementary exterior duality turns Lambda^2(color) into
dual color, and rank-one trace is evaluation. Trace of the transported
endomorphism is exactly the chosen volume applied to W. Thus the kernel
identification and both inverse directions are proved, including the
existing choice of volume, without a normalization assumption.

## Boundary after this result

No new literature input, unproved branching/equivalence/positivity premise,
custom axiom or numerical certificate enters these decompositions.
In particular no remaining `Allowed` or Hom test is asserted to be decided
by this core result alone.

The remaining limited interfaces are now the complete Q-core exterior
branches and a complete positive color coupling rule for the actual reachable
summands across generations/species. The rule must retain simultaneous
color, weak and both spin labels, and prove both witnesses and exclusions.
Symmetric color-square and trace-free color irreducibility, dual-branch
matching and further tensor products have not been inferred from this split.
The previously documented library boundary for that broader coupling
foundation is unchanged; see [the boundary](colored-core-boundary.md).
