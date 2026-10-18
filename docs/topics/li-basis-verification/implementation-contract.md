# Frozen D.38 Implementation Contract

The candidate is the printed arXiv v2 appendix D.1 equation (D.38), not a
package runtime array. Its slots are `Q,Q,E,U`; the repository uses `Q,Q,U,E`.
Angle and square brackets are interpreted as the normalized alternating
SL(2,C) pairings (`eps2`) in independently chosen left and right spinor bases.
The color/weak epsilons likewise use the existing determinant pairings.
These basis choices are the explicit coordinate dictionary, not a claim about
an unprinted numerical epsilon convention or an LSZ amplitude normalization.

## Interfaces And Endpoint

- Encode the daggered singlet gauge carriers as double duals of the existing
  right gauge representations, with residual actions `b.dual`, `d.dual` and
  right Weyl spin. The undaggered gauge representations are their first duals;
  this is the algebraic contragredient convention for the charge-conjugate
  fields. Construct the canonical bidual field equivalences. Arbitrary model
  fields still require explicit equivariant identifications with this dictionary.
- Construct the paper-ordered coefficient and its pure-tensor evaluation from
  the existing normalized gauge/spinor pairings. Prove the singlet transposition
  contributes a minus sign. Include the fermionic minus sign in pullback and
  prove the resulting ordered coefficient equals the repository coefficient.
- Assemble into the independently defined species exterior sector. Its raw
  alternatization evaluates to twice the symmetric ordered coefficient; retain
  this factor explicitly. Reuse the completeness equivalence for both inverses.
- For finite flavor bases `A,B,D`, use the pinned library's `Basis.symmetricPower`
  (unordered pairs) and `Basis.tensorProduct`. Coordinates are explicit matrices
  for `Hom(Sym² A,B ⊗ D)`. For arbitrary residual H the matrix must satisfy
  intertwining equations; unrestricted individual matrix units are not claimed
  invariant. For trivial residual action all matrices are allowed, and matrix
  units give explicit flavor-specified D.38 candidates and a basis certificate.
- Check both coordinate inverse identities in Lean and connect the coordinate
  entries to ordered residual evaluation on basis/dual-basis inputs. No abstract
  basis infrastructure is added. Finite basis inputs restrict only the coordinate
  corollary; the semantic adapter retains the original arbitrary-H assumptions.

Stop before derivatives, EOM/IBP, general amplitude foundations or physical
matching. Strict axiom/import audits, focused builds, full `lake build`, layout,
Markdown links and the existing exact qque sign cross-check are required.
