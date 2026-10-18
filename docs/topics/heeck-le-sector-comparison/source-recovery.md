# Source Recovery And Version Pin

## Verified Metadata

Checked against the primary
[arXiv version history](https://arxiv.org/abs/2604.25134).

- Authors: Julian Heeck and Brandon B. Le.
- Title: *Basis for non-derivative baryon-number-violating operators*.
- Original v1: 28 April 2026.
- Latest version at planning: v2, 6 October 2026, 13:51:52 UTC.
- The v2 metadata describes operator improvements and typo corrections.
- Target pin: [2604.25134v2](https://arxiv.org/abs/2604.25134v2).

The abstract describes non-derivative SMEFT baryon-number violation through
dimension 11 and specified dimension-12 sectors. This is source context only;
it is not the scope of the planned verification.

## Recovered Primary Inputs

Browser retrieval of the [v2 PDF](https://arxiv.org/pdf/2604.25134v2) and
[v2 HTML](https://arxiv.org/html/2604.25134v2) returned cache misses.
The earlier v1 HTML returned not found. The abstract/version page was readable.
Direct download subsequently succeeded for the versioned
[PDF](https://arxiv.org/pdf/2604.25134v2) and
[TeX archive](https://arxiv.org/src/2604.25134v2). SHA-256:

- PDF: `a3ca5ba533c98f513578b491173c1b507130ec5f805ba36ec336da70a67899ff`
- TeX archive: `cfe07c8a0c903ded29add492d603960655dfd940099435d1e2298fd84511e64c`

The TeX `main.tex` was checked against PDF text; the files are disposable
external inputs, not repository dependencies. Section 2.1 fixes epsilon signs
and defines the C bilinear. It explicitly labels flavors as the three
fermion generations. Our comparison uses the algebraic Weyl-epsilon
normalization, not a new four-component Dirac or amplitude theorem.

## Proposed Overlap Inventory

| Existing target | Source entry/location | Current evidence |
|---|---|---|
| DUQL, dimension 6 | Sec. 6, p. 21; `main.tex` 580 | D,U,Q,L; spin (01)(23), weak (23) |
| QQUE, dimension 6 | Sec. 6, p. 21; `main.tex` 581 | Q,Q,U,E; spin (01)(23), weak (01) |
| QQQL, dimension 6 | Sec. 6, p. 21; `main.tex` 582 | Q,Q,Q,L; spin (01)(23), weak (03)(12) |
| DUUE, dimension 6 | Sec. 6, p. 21; `main.tex` 579 | D,U,U,E; spin (01)(23) |
| Specified right-handed u²d⁴, dimension 9 | Sec. 9.4, p. 23; `main.tex` 730–731 | D,U,D,U,D,D; two color contractions |

This proposed inventory is not a set of verified literature comparisons.
No Heeck–Le coverage ledger row is claimed yet. In repository U,D,U,D,D,D
order the six-quark color triples are (134)(025) and (124)(035), with spin
(01)(23)(45). The two species reorders and two bilinear reversals give no
net sign. This source's two compact terms must be compared through flavor
exchange orbits, not counted as two free coordinates at arbitrary multiplicity.
