# Theorem-Driven Constraint Checks

`check_su5_exotic_bounds.py` uses only Python's standard library and the
existing complete-character routines in tools/su6-light-placement-search.
It constructs formal 10/bar5/40/50 characters, reconstructs every SM block,
checks dimensions and sparse chiral-index rows, and compares all Lean literal
profiles. It does not certify actual continuous branching or arbitrary masses.

Run from the repository:

```
PYTHONDONTWRITEBYTECODE=1 python3 tools/theorem-driven-protection-constraints/check_su5_exotic_bounds.py
```

The conclusions about net copy counts follow from exact coefficient rows,
not a numerical cutoff or sample. No third-party dependency is introduced.
