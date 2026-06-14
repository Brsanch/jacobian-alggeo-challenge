# I.1a piece (III) — sheaf-preservation of the internal hom — route doc (2026-06-14)

**Status of I.1a.** Piece (I) (`sheafificationW = isLocal`) and piece (II) (`Closed F`,
the tensor–hom adjunction `tensorLeft F ⊣ [F,-]`) are BUILT and on `main` (@`1ce4866`,
full build 8348 jobs, axioms clean). The **only** remaining content for
`(sheafificationW J R₀).IsMonoidal` — hence for `SheafOfModules.monoidalCategory` and
the bottom brick I.1 — is **piece (III): the internal hom of a sheaf is a sheaf.** This
is the classical theorem *"sheafification of presheaves of modules commutes with ⊗"*
(Stacks 17.16 / EGA 0_I.4.1). mathlib has it **only for the type/abelian-group–valued
`presheafHom`** (`CategoryTheory/Sites/SheafHom.lean`), not for the R₀-linear module hom
over a varying ring. This is a genuine multi-session sub-arc, not a port.

## Why the cheap shortcuts fail (checked 2026-06-14)

- **`toPresheaf` monoidal ⇒ inverse-image monoidal** (`Localization/Monoidal/Basic.lean:71`,
  `MorphismProperty.inverseImage … IsMonoidal`): would give `(sheafificationW).IsMonoidal`
  for free *if* `toPresheaf : PMod(R₀⋙forget₂) ⥤ (Cᵒᵖ ⥤ AddCommGrp)` were monoidal. It is
  **not**: PMod's tensor is the pointwise *module* tensor `M(X) ⊗_{R₀(X)} N(X)`, the AbGrp
  target tensor is `⊗_ℤ`; `toPresheaf` does not preserve `⊗`. DEAD.
- **`transport_isMonoidal`** (`Sites/Monoidal.lean:118`): transports along a cover-dense
  functor between *plain* presheaf categories `Cᵒᵖ ⥤ A`. PMod is not of that form. DEAD.
- **Reuse `Presheaf.IsSheaf.hom` directly** (`Sites/SheafHom.lean:209`): it proves
  `IsSheaf (presheafHom F G)` for `F G : Cᵒᵖ ⥤ A`. But `(internalHom F H).presheaf` is the
  AbGrp of **R₀-linear** PMod-morphisms `(restrict X).obj F ⟶ (restrict X).obj H`, a proper
  sub-object of the type-`presheafHom` (all natural transformations of the underlying
  presheaves). The linearity is the extra, non-trivial content. NOT a direct corollary —
  but `IsSheaf.hom` is the **engine both routes below reuse**.

## The target (exact statement to discharge)

`PresheafOfModules.IsSheaf M := Presheaf.IsSheaf J M.presheaf` (`ModuleCat/Sheaf.lean:35`,
`.presheaf` = the underlying `Cᵒᵖ ⥤ AddCommGrpCat`). The piece needed by `whiskerLeft` is:

> **(III)** For `H : SheafOfModules R`, the PMod `internalHom F ((localInclusion α).obj H)`
> lies in `Set.range (localInclusion α).obj` (it is the restriction of a sheaf of modules).

Equivalently, two sub-facts: (III-a) `Presheaf.IsSheaf J (internalHom F H').presheaf` when
`H'.presheaf` is a sheaf, and (III-b) repackage the resulting `SheafOfModules`-structure as
`(localInclusion α).obj _`. (III-a) is the content; (III-b) is bookkeeping via
`SheafOfModules.fullyFaithfulForget` (`ModuleCat/Sheaf.lean:73`).

`internalHom`, `internalHomObj`, `restrict`, and `internalHomMap_app` are all in
`Submission/Cohomology/PresheafOfModulesInternalHom.lean`; the carrier-diamond idioms are
documented there.

## Route A — direct amalgamation mirror (self-contained, ~250–400 LOC)

Mirror `presheafHom_isSheafFor` (`Sites/SheafHom.lean:172`, with auxiliaries
`exists_app:134`, `app:158`, `app_cond:161`, `PresheafHom.isAmalgamation_iff:104`). The
mathlib proof builds the amalgamated section `Y ↦ (hG g).lift c` from the limit/sheaf
condition `hG` of the target `G` over each slice, then checks naturality + uniqueness.

**What changes for the module hom.** Each `x g hg` is a *PMod-morphism* (R₀-linear), and the
glued section must be R₀-linear too. The lift `(hG g).lift c` is built in
`AddCommGrp`/`Type`; linearity of the result is the extra obligation. It holds because:
each `app hG x hx g` is determined by the equations `app_cond` (which involve only the
*linear* family `x`), and R₀(W)-linearity is a *closed* condition compatible with the
sheaf-determined value — so the amalgamated component inherits linearity from the pieces.
Concretely the new obligation is `app … (r • z) = r • app … z`, discharged from
`app_cond` + the linearity of every `x (p≫g) hp` + the *uniqueness* half of the sheaf
condition for `H` (two sections agreeing on the cover are equal). Risk: dense glue, and the
scalar `r ∈ R₀(W)` varies with the slice, so the linearity bookkeeping is threaded through
every `Over`-reindex.

## Route B — equalizer of `presheafHom` sheaves (shorter if the iso lands, mathlib-backed)

mathlib HAS "a presheaf that is a pointwise limit of sheaves is a sheaf":
`Presheaf.isSheaf_of_isLimit` (`Sites/Limits.lean:136`) + `Sheaf J D` has limits and
`sheafToPresheaf` **creates** them (`Sites/Limits.lean:148,150,161`). So:

1. `presheafHom (toPresheaf F) (toPresheaf H')` is a sheaf of types/AbGrp by
   `Presheaf.IsSheaf.hom` (H'.presheaf a sheaf). Same for `presheafHom ((R₀⊙F)…) (H'…)`,
   where `R₀⊙F` is the presheaf `X ↦ R₀(X) ⊗ F(X)` (needs: tensoring a PMod by the ring
   presheaf — small new infra, or use `F ⊗ (the unit/ring object)`).
2. R₀-linearity of a natural transformation `η` is exactly the equalizer condition
   `act ∘ (R₀⊙η) = η ∘ act : presheafHom(F,H') ⇉ presheafHom(R₀⊙F, H')` (the two ways to
   "scale then map" vs "map then scale").
3. `(internalHom F H').presheaf ≅ equalizer(those two parallel sheaf maps)` — the **load-
   bearing iso**: a PMod-morphism ⟺ a linear natural transformation. Prove via
   `PresheafOfModules.Hom` ext + the slice restriction maps.
4. `Presheaf.isSheaf_of_isLimit` on the equalizer cone (an equalizer is a limit; its legs
   are sheaf maps) ⇒ `(internalHom F H').presheaf` is a sheaf.

**Obstruction (max resolution).** Step 3's iso is where the work concentrates: it must
identify the *set* of PMod-morphisms (a structure with naturality + per-slice linearity)
with the *equalizer set* of the two type-level maps, naturally in `X`, and over a *varying*
R₀. Step 1's `R₀⊙F` requires expressing "tensor a presheaf of modules with the ring
presheaf as a module" — check whether `(restrict X).obj F` tensored with `R₀|` is already
available from `Presheaf/Monoidal.lean` or needs a 1-file helper. If step 3's iso resists,
fall back to Route A.

## The short remainder once piece (III) lands (~40–60 LOC, uses Closed F + piece I)

Mirror `GrothendieckTopology.W.whiskerLeft` (`Sites/Monoidal.lean:132`):

```
lemma sheafificationW.whiskerLeft (hg : sheafificationW J R₀ g) (F) :
    sheafificationW J R₀ (F ◁ g) := by
  rw [sheafificationW_eq_isLocal α]; rintro _ ⟨H, rfl⟩
  -- goal: Bijective (fun (φ : F⊗Y ⟶ (localInclusion α).obj H) => (F ◁ g) ≫ φ)
  -- (localInclusion α).obj H = internalHom-target; by piece (III), internalHom F it is local
  -- transport via (internalHomAdjunction F).homEquiv (homEquiv_naturality_left_symm conjugates
  --   (F ◁ g) ≫ -  to  g ≫ -) ; then sheafificationW.bijective_precomp hg (internalHom-as-sheaf)
```

`(internalHomAdjunction F).homEquiv` and its naturality (`Adjunction.homEquiv_naturality_left_symm`)
are FREE from the `Adjunction` already built — no new lemmas. `whiskerRight` ⟸ `whiskerLeft`
via the PMod braiding (`Presheaf/Monoidal.lean` gives `SymmetricCategory`) +
`MorphismProperty.arrow_mk_iso_iff` (mathlib `Sites/Monoidal.lean:144`). Then
`instance : (sheafificationW J R₀).IsMonoidal := { whiskerLeft … , whiskerRight … }`,
discharging the `variable [...]` in `SheafOfModulesMonoidal.lean` and making
`SheafOfModules.monoidalCategory` + I.1 unconditional.

## Route-B kickoff — de-risking findings (2026-06-14, before any LOC)

Validated against the warm cache:

- **The forgetful map typechecks (alignment is `rfl`).** `pushforward₀CompToPresheaf`
  (`Pushforward.lean:75`) is `Iso.refl`, so `((restrict X).obj F).presheaf =
  (Over.forget X.unop).op ⋙ F.presheaf` definitionally. Hence `internalHom F H .obj X`
  (PMod-morphisms) forgets via `toPresheaf` into `presheafHom (F.presheaf) (H.presheaf) .obj X`
  with no coercion friction. ✓
- **Route B's equalizer legs need infrastructure mathlib LACKS.** Encoding R₀-linearity as
  `presheafHom(F,H) ⇉ presheafHom(R₀⊙F, H)` requires (i) the AbGrp-presheaf tensor `R₀⊙F`
  and (ii) the module action `R₀⊙F ⟶ F` **as a single `Cᵒᵖ ⥤ AddCommGrp` morphism** — neither
  is exposed (greps empty: no `MonoidalClosed`/tensor wrapper readily usable here, no bundled
  action-as-presheaf-map). Both must be BUILT first (~100–150 LOC of setup) before the
  equalizer even types. So Route B's "shorter via `isSheaf_of_isLimit`" advantage is
  front-loaded with real new infra.
- **⚠ Route A may actually be the cleaner tool.** It glues *PMod-morphisms directly* in the
  module category, so the amalgamated section's components come from `H`'s **module-level**
  descent (`(restrict X).obj H` a sheaf of modules ⇒ its slice descent lifts are
  `ModuleCat` morphisms) — R₀-linearity of the glued section is then **automatic**, and NO
  `R₀⊙F` tensor/action is needed. The cost is replicating the dense `presheafHom_isSheafFor`
  glue (~250–400 LOC) rather than reusing it as a black box.

**Recommended first sub-lemma (either route).** `Presheaf.IsSheaf J (presheafHom (F.presheaf)
(H.presheaf))` from `Presheaf.IsSheaf.hom` + the forgetful `internalHom.presheaf ⟶ presheafHom(…)`
mono — both surely-green from the `rfl` alignment — establishes the ambient sheaf and the
embedding. Then the routes diverge: B builds `R₀⊙F` + the equalizer; A replicates the
amalgamation in PMod. **Open decision for the build session:** B (mathlib `isSheaf_of_isLimit`
hook, but `R₀⊙F` infra) vs A (no new infra, but re-derive the glue). Pick after pricing the
`R₀⊙F` action-map construction against the amalgamation replication.

## DONE WHEN

`instance : (sheafificationW J R₀).IsMonoidal` proved (no `sorry`/`axiom`, vacuity 0),
the `variable [(sheafificationW J R₀).IsMonoidal]` in `SheafOfModulesMonoidal.lean` removed,
full build green. Then I.1 (`SheafOfModules` monoidal) is unconditional → I.2 (`Pic`).

## Sources

- mathlib template: `Sites/Monoidal.lean` (whiskerLeft/whiskerRight/monoidal),
  `Sites/SheafHom.lean` (`presheafHom`, `Presheaf.IsSheaf.hom`, `presheafHom_isSheafFor`),
  `Sites/Limits.lean` (`isSheaf_of_isLimit`, sheaf limits).
- repo: `PresheafOfModulesInternalHom.lean` (piece I + internalHom object/functor),
  `PresheafOfModulesClosed.lean` (piece II, `Closed F`),
  `SheafOfModulesMonoidal.lean` (the consumer; the `IsMonoidal` hypothesis to discharge).
- `ModuleCat/Sheaf.lean` (`SheafOfModules`, `isSheaf` = underlying-presheaf sheaf,
  `fullyFaithfulForget`).
