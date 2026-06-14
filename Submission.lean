import Challenge
import Submission.CechModuleCat
import Submission.StructureSheafModule
import Submission.SheafCohomologyModuleCat
import Submission.StructureSheafCohomology
import Submission.Cohomology.LinearH0
import Submission.Cohomology.RegularLocalDomain
import Submission.Cohomology.RegularLocalDomainGeneral
import Submission.Cohomology.SheafOfModulesMonoidal
import Submission.Cohomology.PresheafOfModulesInternalHom
import Submission.Cohomology.PresheafOfModulesClosed
import Submission.Cohomology.IntegralKrullDim
import Submission.Cohomology.DimensionFormula
import Submission.Cohomology.ConormalH1Cotangent
import Submission.Cohomology.CotangentDeltaInjective
import Submission.Cohomology.ConormalToOmega
import Submission.Cohomology.CotangentInequality
import Submission.Jacobian.InvariantFiniteness
import Submission.Jacobian.AffineInvariants
import Submission.Jacobian.AffineQuotient
import Submission.Jacobian.SchemeGroupAction
import Submission.Jacobian.TensorPowerPermAction
import Submission.Jacobian.AffineSymmetricPower
import Submission.Jacobian.AffineQuotientBase
import Submission.Jacobian.AffineSymmetricPowerStructure
import Submission.Jacobian.TensorPowerFiniteType
import Submission.AbelianVariety

/-!
# Submission root

Development modules live under `Submission/` and are imported here. The final
lean-eval deliverable re-declares all 9 holes under `namespace Submission`
(workspace rules: helpers not in mathlib must be inlined into the submission
workspace; `Challenge.lean` is fixed and must not be modified; comparator
runs via `lake test` in the eval workspace).

No `sorry`, no `axiom`, no `ω` as a binder name (Lean v4.30 reserves it).
-/

namespace Submission

open CategoryTheory AlgebraicGeometry

universe u

variable {k : Type u} [Field k]

/-- **Hole 1 — `genus`.** The genus of a smooth proper curve `C` over `k`, defined as
`dim_k H¹(C, 𝒪_C)` (`JacobianAlggeo.genusH1`, the derived-functor sheaf cohomology of
the structure sheaf valued in `ModuleCat k` — Segments 1–2). Signature matches
`AlgebraicGeometry.JacobianChallenge.genus`. The `IsProper`/`Smooth`/`GeometricallyIrreducible`
instances are mandated by the challenge signature; the `Module.finrank` definition is
total and does not consume them (its honest *value* needs Serre finiteness, Segment 3,
and its *correctness* is enforced through hole 4 `smoothOfRelativeDimension_genus`). -/
noncomputable def genus (C : Over (Spec (CommRingCat.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ :=
  JacobianAlggeo.genusH1 C

end Submission
