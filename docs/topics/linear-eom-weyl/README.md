# Linear Equation Systems And Free Weyl Jets

- ID: `linear-eom-weyl`
- Status: completed; integrated and reverified in the derivative/IBP parent
- Result type: proved common linear EOM and actual free Weyl source extension
- Working branch: `proof/linear-eom-weyl`
- Integration target: `proof/derivative-ibp`
- Authorization: user-directed new child, planning and autonomous implementation
- Parent exception: bounded child of the unmerged derivative/IBP parent
- Integration evidence: merged with preserved history into `proof/derivative-ibp`, including the kernel/conjugate child; merged-state gates pass

## Endpoint

Generalize the scalar-symbol equation construction to component-mixing linear
constant-coefficient systems with all ordinary derivative descendants. Recover
the existing scalar relation module, construct actual odd/even on-shell jet
algebras and finite fixed-grade EOM/IBP coefficient descent, and instantiate
the free massless left-chiral Weyl system with the existing actual Pauli and
SL(2,ℂ) actions. The [contract](plan.md) freezes acceptance and stop conditions.

The Weyl endpoint is one chiral free equation in four dimensions, with explicit
source/dual conventions, descendant stability, genuine removal of first-order
relations and a surviving higher-jet family. Right/conjugate or interacting
equations and general EFT enumeration are separate work. Existing scalar,
mixed and spurion proofs/pins remain intact.

## Work And Verification

The parent integration was verified before this branch was created. The common
closure and scalar recovery, actual quotient algebra and EOM/IBP comparison,
bounded spurion interface and actual Weyl consumer are proved. The two explicit
first-order seeds are nonzero off shell and vanish on shell; their wave
consequences and surviving higher-jet family are checked. Source/dual
orientation is reconciled explicitly in the contract.

All acceptance gates pass: 94 Math and 51 physical strict transitive checks,
full `lake build` (7628 jobs), layout and documentation checks. See
[results](results.md), [verification](verification.md) and [sources](references.md).
No implementation obligation remains inside the contract. Its right/conjugate,
interacting, mixed ideal-presentation and physical-comparison boundaries remain
explicit for this original contract. The subsequent parent integration is
recorded below; master integration and remote push are not included.

The [follow-up child](../jet-eom-completion/README.md) is integrated and
reverified in this branch. It proves the mixed ideal presentation, complete
single-field four-dimensional IBP consumer and conjugate Weyl/adjoint extension
under its own contract and verification. The combined tree passes 255 focused
strict checks and the 7637-job full build before integration into this topic's
recorded derivative/IBP parent.

The combined branch is now integrated into `proof/derivative-ibp`. The target
had no independent advance and the merge had no conflicts. The merged parent
passes 625 focused strict checks and the 7637-job full build, with structural
and documentation gates. See [integration verification](verification.md).
