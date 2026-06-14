import Mathlib

/-!
# The Mayer–Vietoris short exact sequence of free `k`-module sheaves

This is brick **(W1)** of the Serre-finiteness arc (route doc
`ROUTE_SERRE_FINITENESS_2026_06_14.md`): the `ModuleCat k`-valued analogue of mathlib's
`AddCommGrpCat`-valued Mayer–Vietoris short exact sequence
(`CategoryTheory/Sites/MayerVietorisSquare.lean`).

For a Mayer–Vietoris square `S` on a site `(C, J)` (e.g. `Opens.mayerVietorisSquare U V` on the curve's
opens site, with `S.X₄ = U ⊔ V = ⊤`), the free-`k`-module sheaves on the representables fit into a short
exact sequence

`0 ⟶ k[X₁] ⟶ k[X₂] ⊞ k[X₃] ⟶ k[X₄] ⟶ 0`   in `Sheaf J (ModuleCat k)`,

where `k[Xᵢ] = (presheafToSheaf J _).obj (yoneda.obj Xᵢ ⋙ ModuleCat.free k)`. Applying the **generic**
contravariant `Ext`-long-exact-sequence (`Abelian.Ext.contravariantSequence`, valid in any abelian
category with `HasExt`) to this short exact sequence — in the `k`-linear Grothendieck-abelian category
`Sheaf J (ModuleCat k)` — yields the Mayer–Vietoris long exact sequence in the `k`-linear sheaf
cohomology `H J k n F` of `SheafCohomologyModuleCat.lean`, the spine of the genus computation
`H¹(C) ≅ coker(H⁰U ⊕ H⁰V ⟶ H⁰(U∩V))`.

The construction is a direct port of mathlib's: every ingredient is **generic over the coefficient
"free" functor**. `ModuleCat.free k ⊣ forget` (`ModuleCat.adj`) makes `ModuleCat.free k` a left
adjoint, so `J.PreservesSheafification (ModuleCat.free k)` is automatic
(`Sites/Adjunction.lean`, `[G.IsLeftAdjoint] ⟹ PreservesSheafification`), which is exactly what the
pushout-of-free-sheaves argument and the coherence iso `presheafToSheafCompComposeAndSheafifyIso`
require.

Foundation; certifies no hole yet (feeds Serre finiteness, Wall 1).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace Submission.MayerVietorisModuleCat

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (k : Type v) [CommRing k] [HasWeakSheafify J (Type v)] [HasSheafify J (ModuleCat.{v} k)]
  (S : J.MayerVietorisSquare)

/-- The free `k`-module functor is a left adjoint (missing as an instance in mathlib at the pin;
`AddCommGrpCat.free` has it). Needed so that `Sheaf.composeAndSheafify J (free k)` preserves colimits
(the pushout) and preserves sheafification. -/
instance : (ModuleCat.free.{v} k).IsLeftAdjoint := (ModuleCat.adj (R := k)).isLeftAdjoint

/-- The free `k`-module functor preserves monomorphisms (missing as an instance in mathlib at the pin;
direct port of the `AddCommGrpCat.free` proof: a mono in `Type` is split off the empty case, and any
functor preserves split monos; on the empty type `free` lands in the zero object). -/
instance : (ModuleCat.free.{v} k).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    by_cases! hX : IsEmpty X
    · constructor
      intros
      apply (IsInitial.isInitialObj (ModuleCat.free.{v} k) _
        ((Types.initial_iff_empty X).2 hX).some).isZero.eq_of_tgt
    · have hf : Function.Injective f := by rwa [← mono_iff_injective]
      obtain ⟨g, hg⟩ := hf.hasLeftInverse
      have : IsSplitMono f := IsSplitMono.mk' { retraction := TypeCat.ofHom g }
      infer_instance

/-- The Mayer–Vietoris square becomes a pushout in `Sheaf J (ModuleCat k)` after applying
`yoneda ⋙ free k ⋙ sheafify`. (`ModuleCat k` port of `isPushoutAddCommGrpFreeSheaf`.) -/
lemma isPushoutModuleCatFreeSheaf :
    (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k) ⋙
      presheafToSheaf J _)).IsPushout :=
  (S.isPushout.map (Sheaf.composeAndSheafify J (ModuleCat.free k))).of_iso
    ((Square.mapFunctor.mapIso
      (presheafToSheafCompComposeAndSheafifyIso J (ModuleCat.free k))).app
        (S.map yoneda))

/-- The Mayer–Vietoris short complex of free `k`-module sheaves:
`k[X₁] ⟶ k[X₂] ⊞ k[X₃] ⟶ k[X₄]`. (`ModuleCat k` port of `MayerVietorisSquare.shortComplex`.) -/
noncomputable def shortComplex : ShortComplex (Sheaf J (ModuleCat.{v} k)) where
  X₁ := (presheafToSheaf J _).obj (yoneda.obj S.X₁ ⋙ ModuleCat.free k)
  X₂ := (presheafToSheaf J _).obj (yoneda.obj S.X₂ ⋙ ModuleCat.free k) ⊞
    (presheafToSheaf J _).obj (yoneda.obj S.X₃ ⋙ ModuleCat.free k)
  X₃ := (presheafToSheaf J _).obj (yoneda.obj S.X₄ ⋙ ModuleCat.free k)
  f :=
    biprod.lift
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₁₂) _))
      (-(presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₁₃) _))
  g :=
    biprod.desc
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₂₄) _))
      ((presheafToSheaf J _).map (Functor.whiskerRight (yoneda.map S.f₃₄) _))
  zero := (S.map (yoneda ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free k) ⋙
      presheafToSheaf J _)).cokernelCofork.condition

set_option backward.isDefEq.respectTransparency false in
instance : Mono (shortComplex k S).f := by
  have : Mono ((shortComplex k S).f ≫ biprod.snd) := by
    dsimp [shortComplex]
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

instance : Epi (shortComplex k S).g :=
  ((shortComplex k S).exact_and_epi_g_iff_g_is_cokernel.2
    ⟨(isPushoutModuleCatFreeSheaf k S).isColimitCokernelCofork⟩).2

/-- The Mayer–Vietoris short complex of free `k`-module sheaves is exact. -/
lemma shortComplex_exact : (shortComplex k S).Exact :=
  ShortComplex.exact_of_g_is_cokernel _
    (isPushoutModuleCatFreeSheaf k S).isColimitCokernelCofork

/-- **(W1) The Mayer–Vietoris short exact sequence of free `k`-module sheaves.**
`0 ⟶ k[X₁] ⟶ k[X₂] ⊞ k[X₃] ⟶ k[X₄] ⟶ 0` in `Sheaf J (ModuleCat k)`. The generic contravariant
`Ext`-long-exact-sequence applied to this is the Mayer–Vietoris long exact sequence in `k`-linear
sheaf cohomology. -/
lemma shortComplex_shortExact : (shortComplex k S).ShortExact where
  exact := shortComplex_exact k S

open CategoryTheory.Abelian in
/-- **(W1) The Mayer–Vietoris long exact sequence in `k`-linear sheaf cohomology.** Applying the
generic contravariant `Ext`-long-exact-sequence to the free-`k`-module-sheaf short exact sequence, in
the `k`-linear Grothendieck-abelian category `Sheaf J (ModuleCat k)`, gives the exact 6-term sequence

`Ext(k[X₄],F,n₀) ⟶ Ext(k[X₂]⊞k[X₃],F,n₀) ⟶ Ext(k[X₁],F,n₀) ⟶[δ] Ext(k[X₄],F,n₁) ⟶ Ext(k[X₂]⊞k[X₃],F,n₁) ⟶ Ext(k[X₁],F,n₁)`.

Since `Ext(k[Xᵢ], F, n)` is the degree-`n` sheaf cohomology of `F` over `Xᵢ` (the
`SheafCohomologyModuleCat.lean` `H` evaluated at `Xᵢ`), this is the Mayer–Vietoris long exact sequence
`Hⁿ(X₄) ⟶ Hⁿ(X₂)⊕Hⁿ(X₃) ⟶ Hⁿ(X₁) ⟶ Hⁿ⁺¹(X₄) ⟶ ⋯`. For the curve's 2-affine cover with `X₄ = U⊔V = ⊤`,
`X₂ = U`, `X₃ = V`, `X₁ = U⊓V`, the `n₀ = 0, n₁ = 1` segment computes `H¹(C)` from `H⁰(U⊓V)` and the
(acyclic) `H¹(U), H¹(V)` — the genus presentation. -/
lemma mayerVietoris_ext_exact [HasExt.{w} (Sheaf J (ModuleCat.{v} k))]
    (F : Sheaf J (ModuleCat.{v} k)) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (Ext.contravariantSequence (shortComplex_shortExact k S) F n₀ n₁ h).Exact :=
  Ext.contravariantSequence_exact _ _ _ _ _

end Submission.MayerVietorisModuleCat
