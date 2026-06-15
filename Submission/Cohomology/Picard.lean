import Submission.Cohomology.SheafificationWMonoidal

/-!
# I.2: the Picard group

The **Picard group** of a monoidal category is the group of isomorphism classes of ⊗-invertible
objects (line bundles, when the category is sheaves of modules). We define it as the **units of the
skeleton monoid**: mathlib's `CategoryTheory.Skeleton.instMonoid` makes the skeleton (iso-classes
under `⊗`) a monoid, and its units `(Skeleton D)ˣ` are exactly the iso-classes admitting a
`⊗`-inverse — i.e. the invertible objects. For a braided/symmetric monoidal category the skeleton is
a *commutative* monoid (`Skeleton.instCommMonoid`), so the Picard group is **abelian** — as it must
be for the Jacobian (an abelian variety) to be its `Pic⁰`.

* `Pic D` — the Picard group of any monoidal category `D` (a `Group`; a `CommGroup` when `D` is
  braided). Reusable, mathlib-PR-grade.
* `SheafOfModules.Pic α` — the Picard group of sheaves of modules over the sheaf of rings `R`
  (presented as the sheafification of the commutative ring presheaf `R₀` via `α`). Built on the
  monoidal structure I.1 (`SheafOfModules.monoidalCategory`), now unconditional thanks to I.1a
  (`sheafificationW_isMonoidal`); it is a **commutative group**, since `SheafOfModules R` is
  symmetric monoidal (the symmetric structure transports through the sheafification localization for
  free, and `PresheafOfModules` is symmetric).

This is the I.2 brick of the Stack-I tower (`docs/SHARED_FOUNDATION_ROUTE_2026_06_13.md`): the
A-vs-B Jacobian-route fork is meant to be revisited here, "once `Pic X` exists". The remaining
Stack-I bricks (I.3 `𝒪(n)` / I.4 ample / I.5 projective morphisms) and the *scheme* structure on
`Pic⁰` (representability — the Jacobian itself) are downstream and not built here.

Single-universe (matching pieces II, III and bricks 4–5). No `sorry`, no `axiom`, no `ω` binders.
-/

open CategoryTheory MonoidalCategory

namespace JacobianAlggeo

/-- The **Picard group of a monoidal category** `D`: the units of its skeleton monoid, i.e. the
isomorphism classes of `⊗`-invertible objects under the tensor product. -/
noncomputable def Pic (D : Type*) [Category D] [MonoidalCategory D] : Type _ :=
  (CategoryTheory.Skeleton D)ˣ

/-- The Picard group of a monoidal category is a group (inverse = the `⊗`-inverse line bundle). -/
noncomputable instance instGroupPic (D : Type*) [Category D] [MonoidalCategory D] :
    Group (Pic D) :=
  inferInstanceAs (Group (CategoryTheory.Skeleton D)ˣ)

/-- The Picard group of a *braided* monoidal category is commutative. -/
noncomputable instance instCommGroupPic (D : Type*) [Category D] [MonoidalCategory D]
    [BraidedCategory D] : CommGroup (Pic D) :=
  inferInstanceAs (CommGroup (CategoryTheory.Skeleton D)ˣ)

section SheafOfModules

universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {R₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J RingCat.{u}}
  (α : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The **Picard group of sheaves of modules** over the sheaf of rings `R`, presented as the
sheafification of the commutative ring presheaf `R₀` along `α`. Unconditional given the data `α`:
the monoidal structure I.1 is made usable by I.1a (`sheafificationW_isMonoidal`). It is the Picard
group of the (symmetric) monoidal category `SheafOfModules R`, taken via the defeq presentation
`LocalizedMonoidal (sheafification α) (sheafificationW J R₀) (Iso.refl _) = SheafOfModules R` so that
the localized monoidal and symmetric instances are used natively (no instance-diamond). -/
noncomputable def _root_.SheafOfModules.Pic : Type _ :=
  haveI := sheafificationW_isMonoidal α
  JacobianAlggeo.Pic
    (LocalizedMonoidal (PresheafOfModules.sheafification.{u} α) (sheafificationW J R₀) (Iso.refl _))

/-- The Picard group of sheaves of modules is a **commutative group** (`SheafOfModules R` is
symmetric monoidal). This is the abelian-group structure that the Jacobian, as `Pic⁰`, refines. -/
noncomputable instance : CommGroup (SheafOfModules.Pic α) :=
  haveI := sheafificationW_isMonoidal α
  inferInstanceAs (CommGroup (JacobianAlggeo.Pic
    (LocalizedMonoidal (PresheafOfModules.sheafification.{u} α) (sheafificationW J R₀) (Iso.refl _))))

end SheafOfModules

end JacobianAlggeo
