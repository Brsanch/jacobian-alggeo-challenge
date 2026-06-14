import Mathlib

/-!
# Krull dimension is invariant under integral extensions

For an integral extension of commutative rings `R → S` the prime spectra have the same
order-theoretic Krull dimension; if the map is in addition injective the two dimensions are
*equal*. This is the classical going-up / incomparability package of Cohen–Seidenberg
(Atiyah–Macdonald ch. 5, Stacks 00OK), and it is the missing link between mathlib's Noether
normalization (`exists_finite_inj_algHom_of_fg`) and the **dimension formula** for a finite-type
algebra over a field — the first absent leaf of the `smooth ⇒ regular local` chain (Wall 2 of the
coherent-cohomology / genus arc).

mathlib at the pin (`5450b53e5ddc`) has the single-step going-up theorem
`Ideal.exists_ideal_over_prime_of_isIntegral` but, as its own source comment records, **no
arbitrary-length-chain version**:

> TODO: Version of going-up theorem with arbitrary length chains (by induction on this)?

and consequently no `ringKrullDim` comparison for integral extensions (`RingTheory/KrullDimension`
has the surjective and ring-equiv cases only). This file supplies both.

* `ringKrullDim_le_of_isIntegral` — contraction of primes is strictly monotone on the spectrum
  (incomparability, via `Ideal.comap_lt_comap_of_integral_mem_sdiff`) ⇒ `dim S ≤ dim R`. Holds for
  *any* integral extension.
* `exists_ltSeries_lift_of_isIntegral` — the arbitrary-length going-up chain lift (the mathlib
  TODO): every chain of primes in `R` lifts, lying over, to a chain of equal length in `S`.
* `le_ringKrullDim_of_isIntegral_of_injective` — ⇒ `dim R ≤ dim S` for injective integral maps.
* `ringKrullDim_eq_of_isIntegral_of_injective` — equality.

This is route-independent, upstreamable mathlib content (a classical theorem completing the
dimension theory of integral extensions), **not** a hole-fill: it certifies no challenge hole.
-/

open Order Ideal PrimeSpectrum

namespace Submission.IntegralKrullDim

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- For an integral extension `R → S`, contraction `P ↦ P ∩ R` is strictly monotone on prime
spectra: a strict inclusion of primes of `S` contracts to a strict inclusion of primes of `R`
(incomparability). Hence `dim S ≤ dim R`. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply krullDim_le_of_strictMono
    (fun P : PrimeSpectrum S => (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R))
  intro P Q hPQ
  rw [← asIdeal_lt_asIdeal] at hPQ ⊢
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt hPQ
  haveI : P.asIdeal.IsPrime := P.isPrime
  exact comap_lt_comap_of_integral_mem_sdiff hPQ.le ⟨hxQ, hxP⟩
    (Algebra.IsIntegral.isIntegral (R := R) x)

/-- **Arbitrary-length going-up** (the mathlib `TODO`): for an injective integral extension
`R → S`, every strictly increasing chain of primes of `R` lifts, lying over, to a chain of the
same length in `S`. Proved by induction on the chain, lifting one prime at a time through the
single-step going-up theorem `Ideal.exists_ideal_over_prime_of_isIntegral`. -/
theorem exists_ltSeries_lift_of_isIntegral [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (p : LTSeries (PrimeSpectrum R)) :
    ∃ q : LTSeries (PrimeSpectrum S),
      q.length = p.length ∧ q.last.asIdeal.comap (algebraMap R S) = p.last.asIdeal := by
  have hker : RingHom.ker (algebraMap R S) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 hinj
  induction p using RelSeries.inductionOn' with
  | singleton x =>
      haveI : x.asIdeal.IsPrime := x.isPrime
      obtain ⟨Q, -, hQp, hQc⟩ := exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal S)
        (by rw [← RingHom.ker_eq_comap_bot, hker]; exact bot_le)
      exact ⟨RelSeries.singleton _ ⟨Q, hQp⟩, rfl, hQc⟩
  | snoc p x hx hp =>
      obtain ⟨q, hlen, hcomap⟩ := hp
      haveI : x.asIdeal.IsPrime := x.isPrime
      have hlt : p.last.asIdeal < x.asIdeal := (asIdeal_lt_asIdeal _ _).2 hx
      have hle : q.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
        rw [hcomap]; exact hlt.le
      obtain ⟨Q, hQge, hQp, hQc⟩ :=
        exists_ideal_over_prime_of_isIntegral x.asIdeal q.last.asIdeal hle
      have hne : q.last.asIdeal ≠ Q := by
        intro h
        rw [← h, hcomap] at hQc
        exact hlt.ne hQc
      have hstrict : q.last < (⟨Q, hQp⟩ : PrimeSpectrum S) :=
        (asIdeal_lt_asIdeal _ _).1 (lt_of_le_of_ne hQge hne)
      refine ⟨q.snoc ⟨Q, hQp⟩ hstrict, ?_, ?_⟩
      · simp [hlen]
      · simpa using hQc

/-- For an injective integral extension, `dim R ≤ dim S` (going-up). -/
theorem le_ringKrullDim_of_isIntegral_of_injective [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  rw [ringKrullDim, ringKrullDim, krullDim, krullDim]
  refine iSup_le fun p => ?_
  obtain ⟨q, hlen, -⟩ := exists_ltSeries_lift_of_isIntegral hinj p
  rw [← hlen]
  exact le_iSup (fun q : LTSeries (PrimeSpectrum S) => (q.length : WithBot ℕ∞)) q

/-- **Krull dimension is invariant under injective integral extensions.** -/
theorem ringKrullDim_eq_of_isIntegral_of_injective [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (le_ringKrullDim_of_isIntegral_of_injective hinj) ringKrullDim_le_of_isIntegral

/-- **Finite Krull dimension of a finitely generated algebra over a field.** Combining the
dimension invariance above with Noether normalization (`exists_finite_inj_algHom_of_fg`): a
nontrivial finite-type `k`-algebra has Krull dimension a genuine natural number — equal to the
dimension `s` of the polynomial subring `k[X₁,…,X_s]` over which it is finite. This is the first
absent leaf of the finite-type-over-field dimension formula. -/
theorem exists_ringKrullDim_eq_of_finiteType (k A : Type*) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] : ∃ s : ℕ, ringKrullDim A = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := Algebra.isIntegral_def.mpr hint
  refine ⟨s, ?_⟩
  rw [← ringKrullDim_eq_of_isIntegral_of_injective (R := MvPolynomial (Fin s) k) (S := A) hinj,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

/-- A nontrivial finite-type algebra over a field has **finite Krull dimension**
(`FiniteRingKrullDim`), the typeclass mathlib's dimension API consumes. Immediate from
`exists_ringKrullDim_eq_of_finiteType`: the dimension is a coerced natural number, hence neither
`⊥` nor `⊤`. (Stated as a theorem, not an instance: the base field `k` is not inferable from `A`.) -/
theorem finiteRingKrullDim_of_finiteType (k A : Type*) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] : FiniteRingKrullDim A := by
  obtain ⟨s, hs⟩ := exists_ringKrullDim_eq_of_finiteType k A
  rw [finiteRingKrullDim_iff_ne_bot_and_top, hs]
  refine ⟨by simp, ?_⟩
  rw [show ((s : WithBot ℕ∞)) = ((s : ℕ∞) : WithBot ℕ∞) by simp, Ne, WithBot.coe_eq_top]
  exact ENat.coe_ne_top s

end Submission.IntegralKrullDim
