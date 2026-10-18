# Covariant Finite Generation: Literature Assessment

## What the literature supplies

The literature supports the finite covariant-module route in the
[support boundary](support-boundary.md). For a complex reductive algebraic
group acting rationally on finite-dimensional spaces V and W, write

    R = (Sym(V*))^G,
    M = (Sym(V*) tensor W)^G.

In characteristic zero, covariants are finitely generated over the invariant
ring R. This supplies a mathematical existence route for finite homogeneous
seeds; it is not a certified seed list for the repository's actual carriers.
The direct sum here consists of finite polynomials, not infinite power series.
Field/dual conventions must be fixed before identifying V or W with operators.

Grinstein, Lu, Merlo and Quilez, arXiv:2312.13349v1, section 2.2.4 explains the
module structure and relations. Section 3.4 explicitly invokes finite
covariant generation for linearly reductive groups, citing Theorem 3.24 of
its reference [7]. That citation locator is inspected in the paper; the
underlying book theorem has not been independently checked here. No exact
Derksen--Kemper theorem number or edition is established by this assessment.
Module rank is not the number of generators, and a generating set need not
be a basis. The paper's MFV conclusions do not establish SM/Higgs support.

Erickson and Hunziker's 2026 article offers constructive Stanley
decompositions for specified classical groups and representations. Its
journal abstract restricts the main family to GL(V), O(V) and Sp(V), with
building blocks made of V and V*, and a further restriction on O(V) targets.
This assessment inspected the journal record and abstract, not the complete
proof or a theorem-level specialization to the SM. It is a candidate source
for explicit weak-group covariants, not a ready-made SM certificate.

## Two different finite tests

If m_1,...,m_r generate M over R, evaluation at a fixed v obeys

    ev_v(sum_i f_i m_i) = sum_i f_i(v) ev_v(m_i).

Consequently its image equals the complex span of the evaluated generators.
For a complex-linear projection P on the target,

    (forall m in M, P(ev_v(m)) = 0)
      iff (forall i, P(ev_v(m_i)) = 0).

This is a direct algebraic consequence of generation and evaluation
compatibility, not a Lean result added in this assessment. It concerns one
fixed vacuum. A nonzero polynomial can vanish there: at v=0 a positive-degree
Higgs invariant vanishes. Thus fixed-vacuum evaluation does not decide
operator nonzero support before evaluating the fields.

For the existing operator-support objective, use the graded module itself.
A proved spanning list gives M=0 iff every seed is zero. A projected test
requires an R-linear projection, or a proof that the projected kernel is
stable under invariant multiplication; arbitrary complex-linear projection
before evaluation does not suffice. Retain bosonic multidegrees, fermion
content and the selected B/L sector. The coefficient ring must preserve
these selections and the residual action. Gauge invariants alone need not
be neutral under an additional residual symmetry.

## Remaining repository obligations

1. Identify the actual mixed exterior/symmetric coefficient carriers with
   the appropriate polynomial covariants, including statistics, local
   Lorentz/gauge invariance and all duals.
2. Prove that the actual actions satisfy the algebraic/reductive hypotheses,
   or prove the needed concrete decomposition directly. An abstract group
   representation does not automatically have a rational algebraic action.
3. Construct homogeneous seeds and certify spanning over the chosen
   invariant ring, preserving the selected gradings and residual action.
4. Certify support of the resulting seeds and connect to the existing
   coefficient-space criterion. Relations matter for independence and exact
   dimensions, although a complete vanishing test needs spanning rather
   than a free basis.

The proved finite fermion universe makes finitely many target modules
available. Finite generation for each would yield a finite reduction of
this fixed derivative-free input. Existence alone supplies neither a
computable cutoff nor the actual finite support table. Generic module rank
also does not certify evaluation rank at every vacuum.

## Recommended bounded continuation

Freeze one fermion content and its actual Higgs/dual covariant module first.
Prove the invariant multiplication and semantic equivalence, then certify a
concrete finite spanning family using the classical invariant-theory route
or explicit weak symmetric-power decomposition. This would address the
missing stage 4B certificate without starting general reductive invariant
theory. A theorem parameter asserting spanning can support a useful
conditional adapter, but does not discharge the spanning premise.

No source theorem is imported as a custom axiom. Stage 4B remains uncertified,
stage 4C unstarted, and the existing candidate counts are unchanged.
