# QQue Exterior Cross-Check

Run from the repository root with Python 3.8 or newer; no extra packages:

```sh
python3 tools/qque/audit_one_generation.py
```

The four exact-integer tests cover exterior exchange/repetition relations,
the one-generation epsilon expansion, its selected four-component projection,
and agreement with full four-slot alternation over all increasing four-element
subsets of 20 component generators (12 Q, 6 up-right, 2 electron-right).
There is no numerical approximation or sampling.

Two normalizations are deliberately retained: unit flavor gives 24 monomials
of absolute coefficient 2; the symmetric flavor coefficient `1*1 + 1*1` gives
absolute coefficient 4. The selected witness has positive coefficient 2 or 4.
Changing the coefficient/sign conventions requires rerunning these tests under
the [workflow](../../docs/architecture/WORKFLOW.md#computational-cross-checks).

The second calculation follows the full 4! alternating-map construction, while
the original calculation expands epsilon contractions in Grassmann generators.
See [the formal correspondence and scope](../../docs/proof/current/applications/Physics/LORENTZ_EXTERIOR_QQUE.md).
This test is not a Lean certificate, not evidence for arbitrary flavor spaces,
and not a UV-model, anomaly or decay-amplitude calculation. General nonzero
existence and actual-light-field transport are proved independently in Lean.

## Two Different Constituents

```sh
python3 tools/qque/audit_pairwise.py
```

Three exact-integer tests cover Q with two flavor components, up-right paired
with the first and electron-right with the second. The symmetric flavor
coefficient is `delta(p,0)delta(r,1) + delta(r,0)delta(p,1)`.
The independent Grassmann expansion agrees with all 4! permutations over all
increasing four-element subsets of 32 component generators. There are 48
nonzero monomials of absolute coefficient 2. Evaluation with the common Q
flavor vector `(1,1)` yields 4, as in the Lean diagonal witness. Repeated
generators and a missing flavor pairing give zero in this concrete test.

This is exhaustive only for the stated finite component model. It is not a
proof of an arbitrary-group assertion or a source satisfying the ambient
GUT/mass/species hypotheses. See the [pairwise topic](../../docs/topics/pairwise-positive-qque/README.md).
The script reuses only the parity/wedge utilities from the one-generation
test, and requires no extra dependencies. Rerun both tests when changing
these contraction, alternation or normalization conventions.

## Li D.38 Local Convention

```sh
python3 tools/qque/audit_li_d38.py
```

Three exact-integer tests compare the printed `Q,Q,E,U` contraction, with
normalized angle/square brackets, to the existing `Q,Q,U,E` Grassmann expansion.
All 48 nonzero epsilon summands are expanded. A negative control omits the
fermionic singlet-transposition sign and produces the negative polynomial.
The raw selected exterior coefficient is 2, with 24 nonzero monomials.
This checks the concrete local dictionary; it does not execute ABC4EFT or
establish a general amplitude/operator correspondence or physical normalization.
Rerun it and the two existing generation checks when changing these conventions.
See [the Lean certificate](../../docs/topics/li-basis-verification/README.md).
