import Mathlib
import Submission.Cohomology.ConormalH1Cotangent
import Submission.Cohomology.CotangentInequality

/-!
# Scalar-transport bridge: `Extension.Cotangent` of the trivial presentation ↔ `CotangentSpace`

This is the `(b5)-finish` residual glue step (i) of the `smooth ⇒ regular local` chain
(route doc §"leaf (b) scoped", residual (i)): it crosses the `ResidueField R ↔ R⧸𝔪` scalar
duality so that the cotangent inequality `embed dim ≤ rel dim` lands on the *certified*
`IsLocalRing.spanFinrank`/`CotangentSpace` objects rather than the bespoke
`Extension.Cotangent` of the trivial presentation.

The key observation is that `Algebra.Extension.Cotangent P` is **definitionally** `P.ker.Cotangent
= Ideal.Cotangent P.ker` (`Extension/Basic.lean:327`). For the trivial extension
`trivExt I = Extension.ofSurjective (mkₐ R I)` (brick (b1)) the kernel is `I` (`trivExt_ker`), so
the bespoke conormal module transports `R`-linearly to `Ideal.Cotangent I` via
`Extension.cotangentEquivCotangentKer` (the `Cotangent.val` iso) followed by `Ideal.Cotangent.equivOfEq`
(the iso induced by `(trivExt I).ker = I`). The `R`-linear equiv is upgraded to a
`(R⧸I)`-linear equiv by `LinearEquiv.extendScalarsOfSurjective` (the quotient map is surjective),
which is exactly what mathlib does in `Module/SpanRankOperations.lean` for the cotangent finrank.

Specialised to `I = 𝔪`, this yields the certified-form inequality

`(maximalIdeal R).spanFinrank ≤ finrank R Ω[R⁄k]`   (separable residue, `IsStandardSmooth`),

i.e. **embedding dimension ≤ relative dimension** on the genuine `IsRegularLocalRing` inputs. The
*only* remaining gap to `IsRegularLocalRing R` (separable residue) is then leaf a′ catenarity, the
single inequality `finrank R Ω[R⁄k] ≤ ringKrullDim R` (the conormal `spanFinrank ≤ finrank Ω`
combined with the always-true `ringKrullDim ≤ spanFinrank` would force equality and regularity via
`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`).

Route-independent foundation; certifies no challenge hole.
-/

open Algebra TensorProduct IsLocalRing

namespace Submission.CotangentSpaceTransport

universe u

variable {R : Type u} [CommRing R]

/-- The `R`-linear scalar-transport equiv. `Algebra.Extension.Cotangent (trivExt I)` is
*definitionally* `Ideal.Cotangent (trivExt I).ker` (`Extension/Basic.lean:327`), so the bespoke
conormal module transports `R`-linearly to `Ideal.Cotangent I` via `cotangentEquivCotangentKer`
(`Cotangent.val`, the defeq identity packaged as a `LinearEquiv`) followed by
`Ideal.Cotangent.equivOfEq` along `(trivExt I).ker = I` (`trivExt_ker`). -/
noncomputable def trivCotangentEquivIdealCotangentR (I : Ideal R) :
    (ConormalH1Cotangent.trivExt I).Cotangent ≃ₗ[R] I.Cotangent :=
  (ConormalH1Cotangent.trivExt I).cotangentEquivCotangentKer ≪≫ₗ
    Ideal.Cotangent.equivOfEq _ _ (ConormalH1Cotangent.trivExt_ker I)

/-- **Scalar-transport equiv.** The conormal module of the trivial presentation of `R⧸I`
(`Algebra.Extension.Cotangent (trivExt I)`) is `(R⧸I)`-linearly isomorphic to `Ideal.Cotangent I`,
upgrading the `R`-linear `trivCotangentEquivIdealCotangentR` via surjectivity of the quotient map
`R → R⧸I` (`LinearEquiv.extendScalarsOfSurjective`). -/
noncomputable def trivCotangentEquivIdealCotangent (I : Ideal R) :
    (ConormalH1Cotangent.trivExt I).Cotangent ≃ₗ[R ⧸ I] I.Cotangent :=
  (trivCotangentEquivIdealCotangentR I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

section Local

variable {k : Type u} [Field k] [IsLocalRing R] [Algebra k R]
  [Algebra.IsStandardSmooth k R] [Algebra.FormallySmooth k (R ⧸ IsLocalRing.maximalIdeal R)]

/-- **(b5)-finish, certified form.** The Zariski cotangent space `𝔪/𝔪²` (over the residue field)
has `finrank` at most the rank of `Ω[R⁄k]` (`= rel dim` for `IsStandardSmooth`). This carries the
(b5)-finish inequality `finrank ((trivExt 𝔪).Cotangent) ≤ finrank Ω` across the scalar transport
onto the certified `IsLocalRing.CotangentSpace`. -/
theorem finrank_cotangentSpace_le_finrank_kaehler :
    Module.finrank (ResidueField R) (CotangentSpace R) ≤ Module.finrank R Ω[R⁄k] := by
  calc Module.finrank (ResidueField R) (CotangentSpace R)
      = Module.finrank (R ⧸ IsLocalRing.maximalIdeal R)
          ((ConormalH1Cotangent.trivExt (IsLocalRing.maximalIdeal R)).Cotangent) :=
        (trivCotangentEquivIdealCotangent (IsLocalRing.maximalIdeal R)).symm.finrank_eq
    _ ≤ Module.finrank R Ω[R⁄k] := CotangentInequality.finrank_conormal_le_finrank_kaehler

/-- **(b5)-finish, `spanFinrank` form.** For a Noetherian local ring with separable residue field
over `k` and `IsStandardSmooth k R`, the minimal number of generators of the maximal ideal (the
embedding dimension) is at most the rank of `Ω[R⁄k]` (the relative dimension). This is the exact
input shape of `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`; closing `smooth ⇒ regular`
(separable residue) reduces to the single remaining catenarity inequality
`finrank R Ω[R⁄k] ≤ ringKrullDim R`. -/
theorem spanFinrank_maximalIdeal_le_finrank_kaehler [IsNoetherianRing R] :
    (IsLocalRing.maximalIdeal R).spanFinrank ≤ Module.finrank R Ω[R⁄k] := by
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact finrank_cotangentSpace_le_finrank_kaehler

end Local

end Submission.CotangentSpaceTransport
