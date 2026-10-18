# Documentation Checks

From the repository root, using Node.js (standard library only):

```sh
node tools/docs/check-links.mjs
node --test tools/docs/test-check-links.mjs
git diff --check
```

The checker inspects tracked and non-ignored new Markdown files, skips deleted
files and fenced code examples, and checks local inline link targets plus
fragments targeting ATX Markdown headings. It is independent of the Lean build.

It does not check external URLs, reference-style links, renderer-specific
extensions, or generated doc-gen4 HTML. It supports the repository's current
inline-link conventions, not arbitrary Markdown syntax. Review moved paths and
claim boundaries separately; passing links do not establish proof correctness.
