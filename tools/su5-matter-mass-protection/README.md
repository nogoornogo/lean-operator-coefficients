# Exact SU(5) Matter/Mass Controls

Run `python3 tools/su5-matter-mass-protection/audit_mass_patterns.py` from
repository root. Python's standard library is the only dependency.

The script uses exact rational Gaussian elimination and integer matrices.
It checks the fixed all-left hypercharge table, the unmixed and specified
mixed 35-dimensional mass ansatz, zero/partial-mass controls and one two-copy
C2 scalar/block-swap flavor intertwiner. No sampling or floating arithmetic.
The expanded controls also check the specified affine rows and a vanishing
row after cancellation. These are subsets of the defined mass ansatz, not a
construction of a UV adjoint coupling.

Hypercharges are 6Y with Q:1, uc:-4, ec:6, dc:2, L:-3, from the actual
SU(5) branching. The mixed rows pair only matching SM species with their dual
by evaluation; this is the stated SM-invariant ansatz, not a proof by checking
only hypercharge. Residual action in the mixed mass example is trivial.
The copy-swap example has zero mass and nontrivial residual C2.

These checks do not prove a UV Yukawa origin, quantum exactness, a complete
Lorentz/exterior coefficient on mixed zero modes, a general mass/action
classification or a decay rate. They are not premises of the Lean proofs.
See [results and scope](../../docs/topics/su5-matter-mass-protection/results.md).
