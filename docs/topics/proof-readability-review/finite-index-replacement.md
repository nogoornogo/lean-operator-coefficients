# SU(6) finite-index row derivation

The five normalized Z5 target obstructions retain their original supplied
branching/light-profile inputs and rational/integer nonexistence statements.
The [certificate source](../../../GUT/SU6/SelectionRules/Models/FiniteIndexCertificate.lean)
now derives annihilation from three primitive row relations, rather than a
closed computation over all target/profile/charge combinations.

Writing a column as \(c\), the relations are

\[
 c_0=c_2,\qquad c_5=c_6,\qquad c_1+c_3+c_4=0.
\]

Two supplied-profile multiplicity identities imply the first two equalities
at arbitrary charge. A three-species multiplicity balance implies the third,
using that cyclic charge negation preserves zero. Profile lookup is confined
to the seven given character lists; charge transport and row annihilation are
proved separately with arbitrary profile/charge variables.

The three functionals are

\[
 A(v)=v_0-v_2,\qquad B(v)=v_1+v_3+v_4,\qquad C(v)=-v_5+v_6.
\]

The five certificates are \((-B,C,A,-A,B)\). A uniform response lemma states
how they act on arbitrary row data. The target is constructed directly from
the complete supplied Q,U,D,L,E profile and its conjugate/opposite-charge
counts. Only the two or three contributing rows of each target are evaluated
to obtain response one. The unchanged finite-sum argument then contradicts
any proposed rational column combination.

The separately stored 5-by-7 certificate and target arrays are removed. Small
explicit source-profile counts remain, with their mathematical role exposed;
this is not a ban on finite arithmetic or a claim to derive arbitrary SU(6)
branching from the lists. The necessary actual-model index transport remains
the explicit `Admitted` application boundary of this certificate.

The [supplemental checker](../../../tools/su6-light-placement-search/check_lean_index_data.py)
still compares static branching/row/light inputs with the independent exact
complete-character screen. It constructs the target and the three semantic
functionals independently, checking 175 column identities and five separations.
It no longer expects evaluated certificate/target arrays in Lean. None of this
Python computation is a theorem premise.

## Verification

The focused source build passed in 21.8 seconds, sampled peak 4,826,020 KiB.
The [strict audit](../../../GUT/SU6/Audit/AuditFiniteIndexCertificate.lean)
retains every earlier root and adds the new row/count/response interfaces:
29 transitive checks passed in the focused build (4.0 seconds, sampled peak
4,637,988 KiB). The axiom allowlist remains `propext`, `Classical.choice`,
`Quot.sound`. No proof limit, dependency pin or allowlist exception was added.
The supplemental exact checker passed. A combined target-case expansion that
hit the default heartbeat budget was split into sparse target-response lemmas;
the budget was not raised.

The full default build passed all 7,453 jobs in 9.8 seconds after focused
builds (sampled peak 6,698,700 KiB), without warnings. A fresh source audit
again passed all 29 checks. Repository checks are repeated at final topic closure.
