# Exact Model Controls

Run `python3 tools/proton-protection-model-checks/audit_models.py` from the repo
root. Seven deterministic unittest controls use only the Python standard
library and exact rational/integer arithmetic. No external package is needed.

- B/L: integral normalization including exotics, complete finite enumeration
  of the specified product-cover torus stabilizer, a nontrivial qque witness,
  uniform three-generation charges, and massive/singular Majorana controls.
- Split SU(5): explicit rectangular kernels, generic mixing and rank-deficient
  negative controls, and parity signs of selected Lagrangian/mass terms.
- Pati–Salam: baryon/charge and pre-EW neutral-kernel controls, plus a selected
  nonzero epsilon-polynomial coefficient of the supplied dimension-five term.

These checks supplement the [Lean certificates](../../GUT/Common/ProtonProtection/ModelControls.lean).
They are not Lean oracles or proofs of UV branching, all mass parameters,
operator completeness, matching or proton stability. The split mass examples
are not certified simultaneous UV coupling choices. Source assignments and
conventions are fixed in the [phase contracts](../../docs/topics/proton-protection-model-checks/phase-contracts.md).
Rerun when these dictionaries, conventions or checked expressions change.
