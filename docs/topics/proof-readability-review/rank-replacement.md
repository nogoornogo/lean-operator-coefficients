# Structural derivation of the rank examples

The [general certificate](../../../Math/LinearAlgebra/ExactRankCertificate.lean)
now has `Certificate.ofActions`: an embedding E, coefficient map R, extraction
P and section S give a certificate from identities on arbitrary vectors,

\[
 E(Rv)=Av,\qquad P(Eu)=u,\qquad R(Su)=u.
\]

The matrix equalities follow from equality of their actions, rather than a
closed product of saved forward/inverse matrices. The existing rank,
field-transport and nullity theorems are unchanged.

The core example uses E(u,w)=(u,w,u+w), R(v)=(v₀+v₂,v₁+v₂),
P(x)=(x₀,x₁) and S(u,w)=(u,w,0). The dependent row and column are
therefore visible in the proof.

The [additional examples](../../../Math/LinearAlgebra/ExactRankCertificateExamples.lean)
use E(u,w)=(u/2+w,u,3u/2+w), R(v)=(v₁+v₃,v₂+v₃),
P(x)=(x₁,x₀−x₁/2) and S(u,w)=(0,u,w,0). The invertible 2-by-2 example
is solved by (y₀,y₁) ↦ ((y₁−3y₀)/2,y₀). These identities are proved by
componentwise symbolic algebra with arbitrary vector entries. Zero and empty
examples factor through the zero-dimensional space. Their matrix inputs and
all six example rank statements are preserved; the generated inverse arrays
and all eighteen closed `decide +kernel` certificate fields are removed.

The [audit](../../../Math/LinearAlgebra/Audit/AuditExactRankCertificates.lean)
retains the earlier twelve roots and also checks the new constructor. Its
layer gate and three-axiom allowlist are unchanged. Final build and repository
verification are recorded in [closure verification](closure-verification.md).
