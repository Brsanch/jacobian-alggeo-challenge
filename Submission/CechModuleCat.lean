import Mathlib

/-!
# M1a — Čech cohomology valued in `ModuleCat k`

The encoding decision recorded in `docs/ROUTE_RESEARCH_2026_06_13.md`: define the
Čech cohomology of a curve as the homology of the Čech cochain complex taken in
`ModuleCat k`, via `CategoryTheory.cechComplexFunctor` (which is generic in a
preadditive target category with products, hence carries the `k`-module structure
the genus DONE WHEN needs — unlike the abelian-group-valued `Sheaf.H`).

This module is the abstract scaffolding: for an arbitrary cover `U : ι → C` and a
`ModuleCat k`-valued presheaf, it packages the Čech cochain complex and its
homology as functors. The geometric instantiation (`𝒪_C`, the two-affine cover of
a smooth proper curve) is M1b; finiteness (Serre) is M1c.

No `sorry`, no `axiom`, no `ω` binders (Lean 4.30 reserves `ω`).
-/

open CategoryTheory CategoryTheory.Limits

namespace JacobianAlggeo

universe w u

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{w} C] [HasFiniteProducts C]
variable {ι : Type w}

/-- The Čech cochain complex functor of a cover `U : ι → C`, valued in `ModuleCat k`:
it sends a presheaf `P : Cᵒᵖ ⥤ ModuleCat k` to its Čech cochain complex (the degree-`n`
term is the product, over `x : Fin (n+1) → ι`, of `P` evaluated on the product of the
`U (x a)`). This is `cechComplexFunctor` specialized to the preadditive target
`ModuleCat k`. -/
noncomputable def cechComplexMod (U : ι → C) :
    (Cᵒᵖ ⥤ ModuleCat.{w} k) ⥤ CochainComplex (ModuleCat.{w} k) ℕ :=
  cechComplexFunctor U

/-- Čech cohomology of a `ModuleCat k`-valued presheaf for the cover `U`, in degree `n`:
the degree-`n` homology of `cechComplexMod`. By construction this is an object of
`ModuleCat k`, so `FiniteDimensional k _` is type-correct (the M1c target). -/
noncomputable def cechH (U : ι → C) (n : ℕ) :
    (Cᵒᵖ ⥤ ModuleCat.{w} k) ⥤ ModuleCat.{w} k :=
  cechComplexMod U ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{w} k) _ n

@[simp]
lemma cechH_obj (U : ι → C) (n : ℕ) (P : Cᵒᵖ ⥤ ModuleCat.{w} k) :
    (cechH U n).obj P = ((cechComplexMod U).obj P).homology n :=
  rfl

/-- **Čech `H⁰` is the module of Čech `0`-cocycles.** The degree-`0` Čech cohomology
of a `ModuleCat k`-valued presheaf is canonically the kernel of the first Čech
coboundary `d⁰ : Č⁰ ⟶ Č¹`. Because the complex is `ℕ`-indexed there is no incoming
differential at degree `0`, so `H⁰` coincides with the cocycles, and the cocycles are
the kernel of `d⁰`. Identifying `d⁰` explicitly with the difference of the two
restriction maps (turning this kernel into the *equalizer of the restriction maps*,
i.e. the global sections of the cover) is the next M1a step. -/
noncomputable def cechHZeroIsoKernel (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} k) :
    (cechH U 0).obj P ≅ kernel (((cechComplexMod U).obj P).d 0 1) :=
  let K := (cechComplexMod U).obj P
  have hnext : (ComplexShape.up ℕ).next 0 = 1 :=
    (ComplexShape.up ℕ).next_eq' (by simp [ComplexShape.up_Rel])
  (CochainComplex.isoHomologyπ₀ K).symm ≪≫
    (K.cyclesIsKernel (i := 0) (j := 1) hnext).conePointUniqueUpToIso
      (limit.isLimit (parallelPair (K.d 0 1) 0))

/-- The cosimplicial object in `ModuleCat k` underlying the Čech complex of `U`:
`⦋n⦌ ↦ ∏ᵢ P(∏ₐ U (i a))` over `i : Fin (n+1) → ι`. By construction
`(cechComplexMod U).obj P = alternatingCofaceMapComplex.obj (cechCosimpl U P)`, so the
Čech coboundaries are the alternating sums of this object's coface maps. -/
noncomputable def cechCosimpl (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} k) :
    CosimplicialObject (ModuleCat.{w} k) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P

/-- **The degree-`0` Čech coboundary is the difference of the two cofaces `δ⁰ - δ¹`.**
This is the first of the two unfolds the equalizer identification needs: the abstract
`d⁰ : Č⁰ ⟶ Č¹` of `cechComplexFunctor` (the alternating coface map complex of
`cechCosimpl`) is `δ 0 - δ 1`, where `δ 0, δ 1 : Č⁰ ⟶ Č¹` are the cosimplicial coface
maps. Identifying these two cofaces *concretely* as the restriction maps onto the
pairwise intersections (via `evalOp`/`mapPower`) — turning `kernel (δ 0 - δ 1)` into the
literal equalizer of the two restriction maps — is the remaining M1a step. -/
lemma cechComplexMod_d_zero_one (U : ι → C) (P : Cᵒᵖ ⥤ ModuleCat.{w} k) :
    ((cechComplexMod U).obj P).d 0 1 = (cechCosimpl U P).δ 0 - (cechCosimpl U P).δ 1 := by
  show (AlgebraicTopology.AlternatingCofaceMapComplex.obj (cechCosimpl U P)).d 0 1
      = (cechCosimpl U P).δ 0 - (cechCosimpl U P).δ 1
  unfold AlgebraicTopology.AlternatingCofaceMapComplex.obj
  rw [CochainComplex.of_d]
  show (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (cechCosimpl U P).δ i) = _
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
    neg_one_zsmul, sub_eq_add_neg]

end JacobianAlggeo
