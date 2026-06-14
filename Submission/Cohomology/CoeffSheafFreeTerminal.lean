import Mathlib
import Submission.SheafCohomologyModuleCat

/-!
# The constant sheaf `k` is the free `k`-module sheaf on a terminal representable

This is the **(W1) connector** of the Serre-finiteness arc (route doc
`ROUTE_SERRE_FINITENESS_2026_06_14.md`): it hooks the Mayer–Vietoris long exact sequence
(`MayerVietorisModuleCat.lean`, whose terms are `Ext(k[Xᵢ], F, n)` with
`k[Xᵢ] = (presheafToSheaf).obj (yoneda.obj Xᵢ ⋙ ModuleCat.free k)`) onto the `k`-linear sheaf
cohomology `H J k n F = Ext(coeffSheaf, F, n)` of `SheafCohomologyModuleCat.lean`.

For a **terminal** object `X` of the site (e.g. `⊤ = U ⊔ V = ` the whole curve, the `X₄` of the
Mayer–Vietoris square), the representable `yoneda.obj X` is the terminal presheaf, so each
`Hom(U, X)` is a singleton and `(Hom(U, X) →₀ k) ≅ k` (`LinearEquiv.finsuppUnique`). Hence the
presheaf `yoneda.obj X ⋙ ModuleCat.free k` is the constant presheaf at `k`, and sheafifying gives the
constant sheaf `coeffSheaf J k`. Therefore

`Ext(k[X], F, n) ≅ Ext(coeffSheaf, F, n) = H J k n F`   (`X` terminal),

so the `X₄ = ⊤` term of the Mayer–Vietoris sequence is exactly `Hⁿ(C, F)`, and the `n = 1` term is
`H1 C`. This is the last spine piece before the genuine walls (W2 affine acyclicity, W3 cokernel
finiteness).

Foundation; certifies no hole yet (feeds Serre finiteness, Wall 1).
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace JacobianAlggeo

universe v u

variable {C : Type v} [SmallCategory.{v} C] {J : GrothendieckTopology C}
  (k : Type v) [Field k] [HasSheafify J (ModuleCat.{v} k)]

/-- For a terminal object `X`, the representable `yoneda.obj X` is the constant presheaf at `PUnit`
(each `Hom(U, X)` is a singleton). Naturality is automatic — `PUnit` is a subsingleton. -/
noncomputable def yonedaTerminalIsoConstPUnit {X : C} (hX : IsTerminal X) :
    yoneda.obj X ≅ (Functor.const Cᵒᵖ).obj PUnit.{v + 1} :=
  NatIso.ofComponents
    (fun U => by
      haveI : Unique ((yoneda.obj X).obj U) := ⟨⟨hX.from U.unop⟩, fun a => hX.hom_ext a _⟩
      exact Equiv.toIso (Equiv.equivPUnit _))
    (fun {U V} _ => by
      haveI : Subsingleton (((Functor.const Cᵒᵖ).obj PUnit.{v + 1}).obj V) :=
        inferInstanceAs (Subsingleton PUnit.{v + 1})
      ext x
      exact Subsingleton.elim _ _)

/-- For a terminal object `X`, the presheaf `yoneda.obj X ⋙ ModuleCat.free k` is isomorphic to the
constant presheaf at `k`: factor `yoneda.obj X ≅ const PUnit` (naturality trivial), whisker by
`ModuleCat.free k`, and use `(PUnit →₀ k) ≅ k` (`Finsupp.LinearEquiv.finsuppUnique`). -/
noncomputable def freeYonedaTerminalIsoConst {X : C} (hX : IsTerminal X) :
    yoneda.obj X ⋙ ModuleCat.free k ≅ (Functor.const Cᵒᵖ).obj (ModuleCat.of k k) :=
  Functor.isoWhiskerRight (yonedaTerminalIsoConstPUnit hX) (ModuleCat.free k) ≪≫
    Functor.constComp (J := Cᵒᵖ) PUnit.{v + 1} (ModuleCat.free k) ≪≫
    (Functor.const Cᵒᵖ).mapIso (Finsupp.LinearEquiv.finsuppUnique k k PUnit.{v + 1}).toModuleIso

/-- **(W1) connector.** For a terminal object `X` of the site, the free `k`-module sheaf on the
representable `yoneda.obj X` is the constant sheaf `coeffSheaf J k`. Combined with
`MayerVietorisModuleCat.mayerVietoris_ext_exact`, this makes the `X₄ = ⊤` term of the Mayer–Vietoris
sequence equal to the `k`-linear sheaf cohomology `Hⁿ(C, F)`. -/
noncomputable def coeffSheafIsoFreeYonedaTerminal {X : C} (hX : IsTerminal X) :
    (presheafToSheaf J (ModuleCat.{v} k)).obj (yoneda.obj X ⋙ ModuleCat.free k) ≅ coeffSheaf J k :=
  (presheafToSheaf J (ModuleCat.{v} k)).mapIso (freeYonedaTerminalIsoConst k hX)

end JacobianAlggeo
