import Submission.AbelianVariety.PointedDiff

/-!
# Tower C — abelian-variety theory + Albanese (aggregator)

Imports the Tower-C development modules so a single
`import Submission.AbelianVariety` from `Submission.lean` makes the whole tower
part of the `lake build` graph (and hence CI-checked).

Serves hole 9 (`exists_unique_ofCurve_comp`, the Albanese universal property),
hole 4's smoothness half, and the group-homomorphism structure hole 3 leans on.
-/
