# Actual 40: Opposite-Species and Same-Orientation Pairing Exclusion

This is a partial checkpoint of the [40 plan](forty-extraction-plan.md).
The subsequent [color/weak result](forty-color-weak-results.md) proves positive
Q/uc multiplicities and zero ec multiplicity. Exact Q/uc counts and the combined
all-mass presentation remain open; complete 40 branching is not claimed.

## Actual proof

[FortyHyperchargeExclusion](../../../GUT/SU5/Branching/FortyHyperchargeExclusion.lean)
constructs the actual Five eigenbasis through `fundamentalEquiv` and tensors
it with the proved Ten eigenbasis. The full ambient Five tensor Ten has
hypercharges -6,-1,4,9. A faithful 31st-root phase, actual basis coordinates
and finite kernel checks prove absence of charges 1,-4,6 in that ambient
representation and its actual wedge kernel.

The chosen 40 is the dual of this kernel. The theorem
`forty_eq_actual_restriction` identifies the SM action used here with the
restriction of the previously constructed SU(5) module. Dual absence is
derived from surjectivity of the shifted finite-dimensional kernel action,
not assumed from a formal character list.

Consequently:

- `opposite_hom_zero` and `opposite_hom_finrank_zero` prove that every source
  with scalar charge -1,4,-6 has zero full Hom multiplicity in the actual 40;
  these include the opposite Q/uc/ec species;
- `no_pairings_forty` and `selected_no_pairings` prove that Q,uc,ec cannot
  form an invariant bilinear mass pairing with this same-orientation 40;
- no matrix entries, scalar representation, VEV, continuous/unitary source
  hypothesis or supplied SM profile is used to prove these conclusions.

This does not exclude mass pairing with conjugate 40. Those possible opposite
partners must be retained in any source/target copy bound. The conclusion
also does not derive a positive Q/uc embedding inside 40.

## Color/weak gate at this checkpoint

The phase argument separates different hypercharges, but not different
color/weak representations at the same hypercharge. The formal profile
suggests two charge-one blocks (Q and a color-sextet doublet), two charge-minus-
four blocks (uc and a weak-triplet color block), and a charge-six color octet.
These descriptions still require actual extraction/equivalence proofs.

The next specific obligation is to relate the original kernel's charge-minus-
six part to the kernel of the color contraction in Color tensor Color-dual,
then derive absence of the electron singlet on its dual. Q/uc extraction must
also use the actual color/weak contractions, prove exhaustiveness and count
all conjugate partners. Epsilon uniqueness is an available asset, but has not
yet been composed into the required kernel branching theorem.

No p/q constraint from formal copies is promoted to an actual extended-family
all-mass theorem at this checkpoint. The new opposite-species/pairing proofs
are usable inputs for that later presentation and record genuine physical
representation progress, not completion of the full requested connection.
