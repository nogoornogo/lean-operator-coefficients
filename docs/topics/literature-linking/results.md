# Literature-linking result and verification

## Disposition of the supplied survey

All 19 distinct sources have a scoped entry in the
[related-literature map](../../proof/RELATED_LITERATURE.md) and a destination
in the existing result guides, dossiers or comparison records. The supplied
survey is an editorial input, not evidence that its comparisons are proved.
No work-date heading, tracking URL, copied search-interface fragment or ranking
of research priority was imported.

Before this pass, 12 sources already had bibliographic links somewhere in
the maintained documents: Li generic EFT, Henning et al., Lehman–Martin,
Grinstein et al., Kobach, Helset–Kobach, Koren, Dreiner–Luhn–Thormeier,
Grzadkowski et al., Liao–Ma, Li dimension nine and Heeck–Le. Their selected
comparison records are reused rather than broadened by a new bibliography.
A name-only software mention was not counted as an existing source citation.

Added seven previously unlinked sources: AutoEFT, Weinberg's original B/L
paper, Rao–Shrock, Lehman's dimension-seven paper, Mac Lane, Fulton–Harris
and Joyal. Each is cited at a relevant existing guide/dossier, not only in the
new map. Joyal is explicitly optional conceptual reading: the repository's
field-species alphabet is not a formal Joyal species functor.

## Bibliographic corrections and boundaries

- Corrected Kobach and Helset–Kobach preprint links in the existing all-degree
  source register from v2 to v1. The primary arXiv records and submission
  histories expose v1 for both sources. This does not retrospectively certify
  the register's unverified signed-charge/grade or flavor-input bridges.
- Used Liao–Ma's full RGE title. The source abstract explicitly uses EOM/Fierz
  reduction and also calculates running; neither its basis count nor RGE is
  imported into the derivative-free bound-seven theorem.
- Kept the Grinstein all-order friendship comparison beside the symmetry
  theorem. The published PDF caveat after Eq. (4.24) was checked directly:
  its bosonic criterion is not an unrestricted fermionic comparison theorem.
- Kept Li's generic EFT source distinct from the dimension-nine source of the
  six-quark printed seeds. The existing Li and Heeck–Le ledgers retain the
  actual bounded semantic comparisons and their limitations.
- Book edition/print information comes from publisher records/contents, not
  the upload year of an eBook. This does not establish proof provenance.

## Inspection depth

Used primary arXiv records/abstracts and publisher bibliographic pages/contents
for new subject links. The published Grinstein caveat was directly inspected;
other detailed comparison locations are attributed to their existing records.
Rao–Shrock publisher metadata/abstract and Weinberg's publisher abstract support
historical context only. Full text of those two was not inspected. Some direct
source requests failed; successful primary records or publisher search-result
metadata were used without claiming that an unavailable full text was read.

No statement that a source contains the identical fixed-SM finite-charge iff,
that either formalization subsumes a paper, or that this is a first/novel result
is added. No new source-to-Lean certificate or external theorem premise is
introduced. Accordingly, no background-only source is added as a verified row
to the literature coverage ledgers. All proof sources are unchanged. A subsequent user request authorized a
root README link to the related-literature map.

## Acceptance checks

```sh
python3 tools/docs/check-work-metadata.py
python3 tools/docs/check-topic-index.py --pending-topic literature-linking
node tools/docs/check-links.mjs
git diff --check
```

Metadata and topic navigation pass. Local links pass for 1,051 Markdown
files, 6,598 local inline links and 110 heading fragments, with zero errors.
Diff whitespace checks pass. All 19 reference
IDs in the literature map are unique; their primary source links and local
destinations are present, without tracking parameters. The pending-topic
exception is only this unmerged topic. No Lean build or axiom audit was rerun;
existing proof verification is not renewed by these editorial changes.
No Lean source, aggregate, toolchain, dependency pin or user-owned docs.zip
changed. The root README gains only the user-requested reference link. No merge, push, software execution or new proof investigation
was performed.

## Three scoped literature findings

The user requested a synthesis of three comparison outcomes, including one
retained proof branch. Added [the findings summary](../../verification/literature-findings.md)
and linked it from the reference map and verification index. The three sources
are Li's selected six-quark printed list, Dutka–Gargalionis's fixed-reading
mass/VEV normalization, and Dev–Mohapatra's conditional coefficient comparison.
The latter two are outside the initial 19-source bibliography inventory.

The summary separates source location, exact consequence, unresolved scope and
integration status. It retains the down-flavor-at-most-three completeness
boundary, the restricted PS normalization family and the source-adoption
condition for the coefficient calculation. It does not label all three as
unconditional paper errors or draw numerical consequences.

Read Dev–Mohapatra closure/model documents directly with git show on the named
branch; confirmed the four listed record paths exist there and are absent from
the current tree, and that its HEAD is not an ancestor of master. No branch
switch, merge, proof copying or build was performed. The page's branch-only
locators are deliberately not broken Markdown links. A snapshot without that
branch does not contain the stronger evidence. Direct requests for its pinned
arXiv record/PDF failed in this pass; no new inspection of those formulas is
claimed. Current-tree coverage retains its earlier algebraic permission scope.

Metadata, topic and diff checks pass. Local links pass for 1,052 Markdown
files, 6,615 local inline links and 110 heading fragments, zero errors.
No Lean build or axiom audit was rerun. No source/pin/root README change,
new coverage certificate, author contact, standalone erratum, merge or push
is included in this summary work.
