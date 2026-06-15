import Mathlib

/-!
# Γ-acyclicity from an acyclic class (the seam-isolated interior of flasque ⇒ acyclic)

This file is the **self-contained homological interior** of the classical theorem *"flasque sheaves
are acyclic for global sections"* (Hartshorne III.2.5 / Godement), needed for the W2 wall of Serre
finiteness (`docs/ROUTE_SERRE_FINITENESS_2026_06_14.md`). It is pure homological algebra in any
abelian category with `HasExt` — **no sheaves, no flasque, no schemes** — so it carries none of the
mathlib seam. The flasque/`ModuleCat k`-sheaf coupling is concentrated into the single hypothesis
`hres` of `acyclic_of_class`, to be discharged separately as the bridge layer.

Fixing an object `X` (think: the constant sheaf, so `Ext X (-) n` is degree-`n` cohomology
`Hⁿ(-)`), an object `F` is **Γ-acyclic** if `Ext X F (n+1) = 0` for all `n`. The engine is the
covariant `Ext` long exact sequence of a short exact sequence `0 → F → I → Q → 0` with `I`
injective:

* `acyclic_one` — base case (`Ext X F 1 = 0`), using the degree-0 `Ext`-surjectivity
  `Ext X I 0 → Ext X Q 0` (Γ-exactness) and `Injective I ⟹ Ext X I 1 = 0`.
* `acyclic_succ` — dimension shift (`Ext X Q (n+1) = 0 ⟹ Ext X F (n+2) = 0`), using
  `Injective I ⟹ Ext X I (n+2) = 0`.
* `acyclic_of_class` — given a class `𝒮` closed under such injective-embedding-with-`𝒮`-cokernel
  short exact sequences (with Γ-exactness), every `F ∈ 𝒮` is Γ-acyclic. The flasque sheaves form
  such a class; supplying `hres` for `𝒮 = flasque` is the remaining seam (bridge) brick, after which
  affine acyclicity `H¹(affine, 𝒪) = 0` (W2) follows by a flasque/Godement resolution.

No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory Abelian Limits

namespace JacobianAlggeo

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] (X : C)

/-- **Dimension shift (step).** For a short exact sequence `0 → F → I → Q → 0` with `I` injective,
if `Ext X Q (n+1) = 0` then `Ext X F (n+2) = 0`. (`Ext X I (n+2) = 0` by injectivity, then the
covariant `Ext` long exact sequence forces `Ext X F (n+2)` into the image of the vanishing
`Ext X Q (n+1)`.) -/
lemma acyclic_succ {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    {n : ℕ} (hQ : ∀ e : Ext.{w} X S.X₃ (n + 1), e = 0) (e : Ext.{w} X S.X₁ (n + 2)) : e = 0 := by
  have hf : e.comp (Ext.mk₀ S.f) (add_zero (n + 2)) = 0 :=
    (e.comp (Ext.mk₀ S.f) (add_zero (n + 2))).eq_zero_of_hasInjectiveDimensionLT 1 (by lia)
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X hS e hf (n₀ := n + 1) (by lia)
  rw [← hx₃, hQ x₃, Ext.zero_comp]

/-- **Base case.** For a short exact sequence `0 → F → I → Q → 0` with `I` injective, if the
degree-0 `Ext`-map `Ext X I 0 → Ext X Q 0` is surjective (the Γ-exactness of the sequence) then
`Ext X F 1 = 0`. -/
lemma acyclic_one {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
    (hΓ : ∀ y : Ext.{w} X S.X₃ 0, ∃ z : Ext.{w} X S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y)
    (e : Ext.{w} X S.X₁ 1) : e = 0 := by
  have hf : e.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    (e.comp (Ext.mk₀ S.f) (add_zero 1)).eq_zero_of_hasInjectiveDimensionLT 1 (by lia)
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ X hS e hf (n₀ := 0) (by lia)
  obtain ⟨x₂, hx₂⟩ := hΓ x₃
  rw [← hx₃, ← hx₂, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- **Γ-acyclicity from an acyclic class.** If every object of a class `𝒮` admits a short exact
sequence `0 → F → I → Q → 0` with `I` injective, cokernel `Q ∈ 𝒮`, and the degree-0 `Ext`-map
`Ext X I 0 → Ext X Q 0` surjective, then every `F ∈ 𝒮` is Γ-acyclic: `Ext X F (n+1) = 0` for all
`n`. The flasque sheaves are such a class; this is the self-contained interior of flasque ⇒ acyclic
(W2 of Serre finiteness), with the entire flasque/sheaf seam isolated into the hypothesis `hres`. -/
theorem acyclic_of_class (𝒮 : C → Prop)
    (hres : ∀ F, 𝒮 F → ∃ S : ShortComplex C, S.ShortExact ∧ Injective S.X₂ ∧
      S.X₁ = F ∧ 𝒮 S.X₃ ∧
        (∀ y : Ext.{w} X S.X₃ 0, ∃ z : Ext.{w} X S.X₂ 0, z.comp (Ext.mk₀ S.g) (add_zero 0) = y)) :
    ∀ (n : ℕ) (F : C), 𝒮 F → ∀ e : Ext.{w} X F (n + 1), e = 0 := by
  intro n
  induction n with
  | zero =>
    intro F hF e
    obtain ⟨S, hS, hInj, rfl, _, hΓ⟩ := hres F hF
    haveI := hInj
    exact acyclic_one X hS hΓ e
  | succ n ih =>
    intro F hF e
    obtain ⟨S, hS, hInj, rfl, hQ, _⟩ := hres F hF
    haveI := hInj
    exact acyclic_succ X hS (ih S.X₃ hQ) e

end JacobianAlggeo
