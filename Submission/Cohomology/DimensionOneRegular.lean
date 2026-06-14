import Mathlib
import Submission.Cohomology.CotangentSpaceTransport

/-!
# A standard-smooth local domain of relative dimension one is regular

This closes the relative-dimension-one case of `smooth ⇒ regular local` — the case the curve needs —
**without** the general dimension formula / catenarity. The general case bottoms out in the Krull
going-down theorem for an integrally-closed base (the dimension formula `height 𝔪 = dim A` for
finite-type `k`-domains), which is **absent** at the pin: mathlib derives `Algebra.HasGoingDown`
only `of_flat` (`Ideal/GoingDown.lean:153`), and Noether normalization `k[x] ↪ A` is integral but
not flat unless `A` is already Cohen–Macaulay — circular with regularity. See route doc §"leaf a′
catenarity" / `LEAP_QUEUE §5`.

The relative-dimension-**one** case sidesteps that wall entirely. For a local *domain* `R` that is
standard smooth of relative dimension `1` over `k` (with separable residue field — the (b3) gate),
the Krull dimension is *derived*, not assumed:

* if `R` is a field, it is a regular local ring trivially (a field is a PID);
* otherwise `𝔪 ≠ ⊥`, so the chain `⊥ ⊊ 𝔪` forces `height 𝔪 ≥ 1`, i.e. `ringKrullDim R ≥ 1`
  (`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`); combined with the cotangent bound
  `spanFinrank 𝔪 ≤ finrank R Ω[R⁄k] = 1` (this session's `CotangentSpaceTransport` brick +
  `IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`), `spanFinrank 𝔪 ≤ 1 ≤ ringKrullDim R`,
  and `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` closes it.

This is honest content (the dimension is derived from the not-a-field dichotomy, never assumed —
assuming `ringKrullDim R = 1` would be a renamed leaf a′). It is also genuinely more general than the
curve: any relative-dimension-one standard-smooth local domain with separable residue is regular.
Relative dimension `≥ 2` cannot be reached this way — `ringKrullDim R ≥ 2` is exactly the going-down
content the elementary `⊥ ⊊ 𝔪` chain does not supply.

The remaining external input to connect this to the curve's scheme is the scheme-smooth ⟹ local-ring
`IsStandardSmoothOfRelativeDimension` AG→CA bridge (to discharge the hypotheses from the curve's
`SmoothOfRelativeDimension 1`).

Route-independent foundation; certifies no challenge hole.
-/

open Algebra IsLocalRing

namespace Submission.DimensionOneRegular

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]

/-- The maximal ideal of a local **domain** that is not a field has height `≥ 1`: the
only minimal prime of a domain is `⊥`, and `𝔪 ≠ ⊥`. -/
theorem one_le_primeHeight_maximalIdeal (hne : IsLocalRing.maximalIdeal R ≠ ⊥) :
    (1 : ℕ∞) ≤ (IsLocalRing.maximalIdeal R).primeHeight := by
  rw [ENat.one_le_iff_ne_zero, Ne, Ideal.primeHeight_eq_zero_iff,
    IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]
  exact hne

/-- A Noetherian local **domain** that is not a field has `ringKrullDim R ≥ 1`. -/
theorem one_le_ringKrullDim (hne : IsLocalRing.maximalIdeal R ≠ ⊥) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim R := by
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, Ideal.height_eq_primeHeight]
  exact_mod_cast one_le_primeHeight_maximalIdeal hne

/-- **Relative-dimension-one `smooth ⇒ regular`.** A Noetherian local domain that is standard smooth
of relative dimension `1` over a field `k`, with separable (formally smooth) residue field, is a
regular local ring. The Krull dimension is derived from the not-a-field dichotomy — never assumed. -/
theorem isRegularLocalRing_of_isStandardSmoothOfRelativeDimension_one
    (k : Type u) [Field k] [IsNoetherianRing R] [Algebra k R]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k R]
    [Algebra.FormallySmooth k (R ⧸ IsLocalRing.maximalIdeal R)] :
    IsRegularLocalRing R := by
  haveI : Algebra.IsStandardSmooth k R := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  -- relative dimension one ⟹ `Ω[R⁄k]` has rank (hence finrank) `1`
  have hrank : Module.rank R Ω[R⁄k] = 1 :=
    IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1
  have hfin : Module.finrank R Ω[R⁄k] = 1 := by
    simp [Module.finrank, hrank]
  -- cotangent bound (this session's scalar-transport brick): `spanFinrank 𝔪 ≤ finrank Ω = 1`
  have hsp : (IsLocalRing.maximalIdeal R).spanFinrank ≤ 1 := by
    have h := Submission.CotangentSpaceTransport.spanFinrank_maximalIdeal_le_finrank_kaehler
      (k := k) (R := R)
    rwa [hfin] at h
  by_cases hfield : IsField R
  · -- a field is a regular local ring (it is a PID)
    let _ := hfield.toField
    infer_instance
  · -- not a field ⟹ `ringKrullDim R ≥ 1 ≥ spanFinrank 𝔪`
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    have hne : IsLocalRing.maximalIdeal R ≠ ⊥ := by
      rw [Ne, ← IsLocalRing.isField_iff_maximalIdeal_eq]
      exact hfield
    calc ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞)
        ≤ (1 : WithBot ℕ∞) := by exact_mod_cast hsp
      _ ≤ ringKrullDim R := one_le_ringKrullDim hne

end Submission.DimensionOneRegular
