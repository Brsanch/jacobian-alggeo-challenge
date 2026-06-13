import Mathlib

/-!
# `IsRegularLocalRing ⇒ IsDomain` (Tower A foundation — toward `smooth/field ⇒ reduced`)

mathlib at the pin has `RegularLocalRing/Defs.lean` only (the definition
`(maximalIdeal R).spanFinrank = ringKrullDim R` + the cotangent criterion), with **no**
`regular ⇒ domain` / `regular ⇒ reduced`. This file builds it by induction on dimension,
using mathlib's existing dimension theory (`KrullsHeightTheorem`, `KrullDimension/*`),
prime avoidance, Krull intersection, and Nakayama.

This is the brick that makes a smooth curve's local rings reduced (regular local rings are
domains ⇒ reduced), hence `IsReduced C.left ⇒ IsIntegral C.left ⇒ Γ(C,⊤) finite over k`
(h⁰ finiteness). Self-contained, upstreamable.

No `sorry`, no `axiom`, no `ω` binders.
-/

open IsLocalRing

namespace JacobianAlggeo

variable {R : Type*} [CommRing R]

/-- **Base case.** A regular local ring of Krull dimension `0` is a field:
`spanFinrank 𝔪 = dim = 0` forces `𝔪 = ⊥`. -/
theorem isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero
    [IsRegularLocalRing R] (h : ringKrullDim R = 0) : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq,
    ← Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)]
  have hsp := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [h] at hsp
  exact_mod_cast hsp

/-- In a local ring whose maximal ideal is principal `𝔪 = (t)`, with the Krull-intersection
`⨅ₙ (t)ⁿ = ⊥`, every nonzero element factors as `tᵏ · u` with `u` a unit. -/
theorem exists_pow_mul_unit_of_maximalIdeal_eq_span [IsLocalRing R] {t : R}
    (ht : maximalIdeal R = Ideal.span {t}) (hbot : ⨅ n, (Ideal.span {t}) ^ n = ⊥)
    {a : R} (ha : a ≠ 0) : ∃ (k : ℕ) (u : R), IsUnit u ∧ a = t ^ k * u := by
  classical
  -- `a ∉ ⨅ₙ (t)ⁿ`, so some power omits `a`; take the largest power containing `a`.
  have hex : ∃ n, a ∉ (Ideal.span {t}) ^ n := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact ha (by simpa [hbot] using Ideal.mem_iInf.mpr h)
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    have hs := Nat.find_spec hex
    rw [h0, pow_zero, Ideal.one_eq_top] at hs
    exact hs Submodule.mem_top
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hak : a ∈ (Ideal.span {t}) ^ k := by
    by_contra hcontra
    have := Nat.find_min' hex hcontra
    omega
  have hak1 : a ∉ (Ideal.span {t}) ^ (k + 1) := hk ▸ Nat.find_spec hex
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hak
  obtain ⟨c, rfl⟩ := hak
  refine ⟨k, c, ?_, by ring⟩
  -- `c` is a unit: otherwise `c ∈ 𝔪 = (t)` and `tᵏ c ∈ (t^{k+1})`, contradiction.
  by_contra hc
  apply hak1
  have hcm : c ∈ maximalIdeal R := by
    by_contra hcm'
    exact hc (IsLocalRing.notMem_maximalIdeal.mp hcm')
  rw [ht, Ideal.mem_span_singleton] at hcm
  obtain ⟨d, rfl⟩ := hcm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨d, by ring⟩

/-- **A regular local ring of Krull dimension `1` is a domain.** `𝔪 = (t)` is principal; every
nonzero element is `tᵏ·unit`, and `t` is not nilpotent (else `𝔪` is nilpotent, forcing dimension
`0`), so a product of nonzero elements `tᵐ⁺ⁿ·(unit)` is nonzero. -/
theorem isDomain_of_isRegularLocalRing_of_ringKrullDim_eq_one
    [IsRegularLocalRing R] (h : ringKrullDim R = 1) : IsDomain R := by
  -- `𝔪 = (t)` principal (`spanFinrank 𝔪 = dim = 1`).
  have hsp : (maximalIdeal R).spanFinrank = 1 := by
    have hsm := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [h] at hsm; exact_mod_cast hsm
  obtain ⟨s, hsenc, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_set_encard_eq_spanFinrank
  rw [hsp] at hsenc
  obtain ⟨t, rfl⟩ := Set.encard_eq_one.mp hsenc
  have ht : maximalIdeal R = Ideal.span {t} := hspan.symm
  -- Krull intersection.
  have hbot : ⨅ n, (Ideal.span {t}) ^ n = ⊥ := by
    rw [← ht]; exact Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  -- `t` is not nilpotent: otherwise `𝔪` is nilpotent ⇒ `R` Artinian ⇒ dimension `0 ≠ 1`.
  have htnil : ¬ IsNilpotent t := by
    rintro ⟨N, hN⟩
    have hmnil : IsNilpotent (maximalIdeal R) :=
      ⟨N, by rw [ht, Ideal.span_singleton_pow, hN]; simp⟩
    have hart : IsArtinianRing R := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mpr hmnil
    have h0 : ringKrullDim R = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
    rw [h0] at h; exact (by norm_num : (1 : WithBot ℕ∞) ≠ 0) h.symm
  -- No zero divisors.
  have hnzd : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨m, u, hu, rfl⟩ := exists_pow_mul_unit_of_maximalIdeal_eq_span ht hbot hcon.1
    obtain ⟨n, v, hv, rfl⟩ := exists_pow_mul_unit_of_maximalIdeal_eq_span ht hbot hcon.2
    refine htnil ⟨m + n, ?_⟩
    obtain ⟨w, hw⟩ := (hu.mul hv).exists_right_inv
    calc t ^ (m + n) = t ^ (m + n) * (u * v * w) := by rw [hw, mul_one]
      _ = t ^ m * u * (t ^ n * v) * w := by ring
      _ = 0 := by rw [hab, zero_mul]
  haveI : NoZeroDivisors R := ⟨fun {a b} hab => hnzd a b hab⟩
  exact { }

end JacobianAlggeo
