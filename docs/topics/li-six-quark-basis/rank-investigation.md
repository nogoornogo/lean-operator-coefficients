# Bounded Local Rank Investigation

This document preserves the exploratory checkpoint. The user subsequently
approved option 1 below. The extended Lean certificate and physical witness
are now recorded in the [proof dossier](../../proof/current/applications/Physics/LI_SIX_QUARK_BASIS.md).
The unproved-boundary statements below describe that earlier checkpoint,
not the current endpoint. The four-component convention boundary remains.

## Question And Frozen Scope

Can the ten printed candidates in Li et al., arXiv:2007.07899v1,
equation (5.63), span the full local permutation representation needed for
arbitrary distinct up/down flavor carriers? The user authorized this bounded
decomposition check, not a restriction to three generations.

## Reproducible Diagnostic

Run from the repository root:

```sh
python3 tools/li-six-quark-check.py
```

The script uses only Python's standard library and exact integers/rationals.
It evaluates epsilon products on five independent color and five independent
Weyl probes. The tensor-product probe matrix has rank 25. It transcribes the
ten seeds and normally filled tableaux from the visually inspected printed
page, uses paper slot order `(D,D,D,D,U,U)`, and includes the fermionic sign
when transferring flavor permutations onto local slots. It tests both
row-column and column-row composition orders. Normalizing a nonzero Young
symmetrizer does not alter these ranks.

| Control or candidate span | Rank |
|---|---:|
| Five-color times five-Weyl basis | 25 |
| Full S4×S2 orbit of the bare seeds | 25 |
| Ten projected seeds | 10 |
| Full S4×S2 orbit of the ten projected seeds, either order | 24 |
| Previous orbit plus down `(1,1,1,1)` / up `(2)` projection | 25 |

All ten projected seeds and the extra projection are nonzero. The extra
projection uses the local character trivial on S4 and sign on S2; after the
fermionic twist this corresponds to alternating down flavor and symmetric up
flavor. The script asserts the listed ranks rather than merely printing them.

An independent dimension warning comes directly from the printed shapes:
their Specht dimensions, counting repeated copies, sum to
`2*3 + 2*3 + 2*1 + 3 + 2*2 + 3 = 24`, not 25.
The extra alternating-down flavor component disappears when the down carrier
has dimension at most three. Thus a three-generation application need not
expose this discrepancy.

## Source And Trust Boundary

[The pinned paper](https://arxiv.org/pdf/2007.07899v1#page=46) supplies the
candidate data, not an assumed completeness theorem. Section 5.1 describes
counts as functions of generation number and then specializes to one and
three; the inspected text did not establish a restriction explaining this
particular ten-term list. This is not a claim that all versions or the authors'
software have an error.

The calculation is **not a Lean proof**. A complete four-component C-matrix
normalization dictionary, the physical exterior transport, and a kernel-checked
certificate that the extra component survives for a specified flavor carrier
remain unproved here. Consequently no new theorem, physical counterexample,
or assumptions-ledger result is claimed. Existing six-quark completeness
theorems are unchanged.

## Stop Gate And Options

The arbitrary-multiplicity ten-candidate endpoint is not supported by this
diagnostic. Continuing requires choosing one of:

1. Retain arbitrary multiplicity and investigate an extended eleven-component
   certificate, distinguishing the added component from the printed list.
2. Restrict the comparison to down dimension at most three and prove that the
   omitted component vanishes, then certify the ten printed components.

Neither is adopted silently. The original general-flavor inverse is not
reported complete. This diagnostic is retained as a reproducible checkpoint;
no dependency or Lean toolchain change is required.

## Verification

The command above passes. No Lean sources were edited and no Lean build or
axiom audit was rerun; no proof baseline is changed. Local Markdown links and
`git diff --check` are checked for this checkpoint.
