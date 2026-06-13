import Mathlib

/-!
# Noether's finiteness theorem for the invariants of a finite group action

For a finite group `G` acting by `R`-algebra automorphisms on a commutative ring `B` that
is of finite type over a commutative ring `R`, the invariant subalgebra `B^G`
(`FixedPoints.subalgebra R B G`) satisfies the two Noether finiteness properties:

* `moduleFinite_of_finiteType` — `B` is module-finite over `B^G`; and
* `finiteType_fixedPoints` — if `R` is Noetherian, `B^G` is of finite type over `R`
  (Emmy Noether, *Der Endlichkeitssatz der Invarianten endlicher Gruppen*, Math. Ann. 1926).

These are the affine building block of the finite-group quotient scheme `Spec(B^G)` of
`Spec B` — the foundation `Sym^d C := C^d / S_d` (route-doc milestone M3) sits on. They are
also route-independent, standalone mathlib-PR-shaped statements (a missing classical
theorem at the pin), and are NOT used to commit the challenge to the symmetric-powers
route — see `docs/ROUTE_RESEARCH_2026_06_13.md` §"TOWER B survey".

Everything is assembled from mathlib at the pin:
* the invariant subalgebra `FixedPoints.subalgebra`;
* `Algebra.IsInvariant.isIntegral` — `B` is integral over `B^G` for finite `G` (via the
  characteristic polynomial `∏_{g} (X - g • b)`, whose coefficients are `G`-invariant);
* `Algebra.IsIntegral.finite` — integral + finite-type ⇒ module-finite;
* `Algebra.fg_of_fg_of_fg` — the Artin–Tate lemma.
-/

namespace AlgebraicGeometry.JacobianChallenge.InvariantFiniteness

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- The invariant subalgebra `B^G ⊆ B` is the ring of invariants in the sense of
`Algebra.IsInvariant`: every `G`-fixed element of `B` is the image of an element of `B^G`
(here, itself). -/
instance isInvariant_fixedPoints :
    Algebra.IsInvariant (FixedPoints.subalgebra R B G) B G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

/-- `B` is integral over its invariant subalgebra `B^G`: for finite `G`, every `b : B` is a
root of the monic characteristic polynomial `∏_{g} (X - g • b)`, whose coefficients lie in
`B^G`. This is `Algebra.IsInvariant.isIntegral`. -/
theorem isIntegral_fixedPoints : Algebra.IsIntegral (FixedPoints.subalgebra R B G) B :=
  Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R B G) B G

/-- **Noether finiteness, part 1.** If `B` is of finite type over `R`, then `B` is
module-finite over its invariant subalgebra `B^G`. (Integral over `B^G` + finite type over
`B^G` ⇒ module-finite over `B^G`.) -/
theorem moduleFinite_of_finiteType [Algebra.FiniteType R B] :
    Module.Finite (FixedPoints.subalgebra R B G) B := by
  have hI : Algebra.IsIntegral (FixedPoints.subalgebra R B G) B := isIntegral_fixedPoints R B G
  have hFT : Algebra.FiniteType (FixedPoints.subalgebra R B G) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (FixedPoints.subalgebra R B G) B
  exact Algebra.IsIntegral.finite

/-- **Noether finiteness, part 2 (Emmy Noether, 1926).** If `R` is Noetherian and `B` is of
finite type over `R`, then the invariant subalgebra `B^G` is of finite type over `R`.
Proof: Artin–Tate applied to `R ⊆ B^G ⊆ B` (`R` Noetherian, `B` finite-type over `R`, `B`
module-finite over `B^G` by part 1). -/
theorem finiteType_fixedPoints [IsNoetherianRing R] [Algebra.FiniteType R B] :
    Algebra.FiniteType R (FixedPoints.subalgebra R B G) := by
  have hBfin : Module.Finite (FixedPoints.subalgebra R B G) B := moduleFinite_of_finiteType R B G
  refine ⟨fg_of_fg_of_fg (A := R) (B := FixedPoints.subalgebra R B G) (C := B) ?_ ?_ ?_⟩
  · exact ‹Algebra.FiniteType R B›.out
  · exact hBfin.fg_top
  · exact Subtype.val_injective

end AlgebraicGeometry.JacobianChallenge.InvariantFiniteness
