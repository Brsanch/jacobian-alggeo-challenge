# 🟢 ROUND 3 ENTRY (2026-06-14) — INTEGRATOR + I.1a/TOWER-A, in this canonical checkout

You are the fresh integrator + Tower-A/I.1a session, on `main` @ `07c0766` (clean tree, all pushed).
A **parallel Stack-II / Serre-finiteness session is now running** (started 2026-06-14) — coordinate
via the integrator role below; do NOT duplicate its Front-B / Serre work. Control room:
`…/jacobian-alggeo-parallel/PARALLEL_PLAN.md`.

> **ROUND-3 ENTRY STATE (2026-06-14, `main` @ `07c0766`):**
> - **I.1a piece (II) `Closed F` DONE** (tensor-hom adjunction `tensorLeft F ⊣ [F,-]`) —
>   `Submission/Cohomology/PresheafOfModulesClosed.lean`, full build green, axioms clean. See the
>   I.1a block further down.
> - **✅ I.1a COMPLETE (2026-06-14) — `(sheafificationW J R₀).IsMonoidal` PROVED**, sorry/axiom-free,
>   vacuity-0, single-universe. All five bricks done:
>   `Submission/Cohomology/PresheafOfModulesSheafHom.lean` = bricks 1–3 (`ambient_isSheaf`, `toAmbient`,
>   **`internalHom_isSheaf`** = Stacks 17.16);
>   `Submission/Cohomology/SheafificationWMonoidal.lean` = bricks 4–5
>   (`mem_isoClosure_of_isSheaf` = PMod-sheaf⟹local-object, `sheafificationW_whiskerLeft`/`Right`,
>   **`sheafificationW_isMonoidal`**). This **discharges the `[(sheafificationW J R₀).IsMonoidal]`
>   hypothesis of `SheafOfModules.monoidalCategory`** (given the sheafification data `α`, via
>   `haveI := sheafificationW_isMonoidal α`) → **I.1 (`SheafOfModules` monoidal) is now usable
>   unconditionally** at single-universe sites (the curve's structure sheaf).
>   **⚠ Universe caveat:** the I.1a chain is single-universe (forced by `isSheaf_iff_isSheaf_forget`);
>   the consumer is multi-universe. The single-universe instance discharges it at single-universe
>   instantiations (the actual use); literally removing the multi-universe `variable` would need
>   multi-universe `internalHom_isSheaf` (hits the forget-sheaf universe wall). Detail + reusable
>   carrier-diamond techniques: `docs/PIECE_III_SHEAF_PRESERVATION_ROUTE_2026_06_14.md` (top §).
> - **✅ I.2 (`Pic`) DONE (2026-06-15)** — `Submission/Cohomology/Picard.lean`, sorry/axiom-free,
>   vacuity-0, single-universe. `JacobianAlggeo.Pic D` = Picard group of any monoidal category `D`
>   (= units of mathlib's skeleton monoid; `Group`, and `CommGroup` when `D` is braided — reusable,
>   mathlib-PR-grade). `SheafOfModules.Pic α` = the Picard group of sheaves of modules, a
>   **commutative group**, unconditional given `α` (uses I.1a `sheafificationW_isMonoidal`; abelian
>   because `SheafOfModules R` is symmetric monoidal — symmetric transports through the localization
>   for free). Stack I now stands at **I.0 ✓ I.1 ✓ I.2 ✓** of ~6.
>   **NEXT — the A-vs-B fork is now reachable** (the route doc says revisit it "once `Pic X` exists",
>   which it now does). Then the shared deep walls, in rough order of leverage:
>   **I.3/I.4/I.5 = ample line bundles + projective morphisms** (the single biggest *shared* blocker —
>   gates Stack I *and* Tower B globalization P3/P5; mathlib has nothing) and **II.1 = Serre finiteness**
>   `FiniteDimensional k (H1 C)` (gates genus-value/hole-1 + RR). Note I.2 gives `Pic` as an abstract
>   group only — the *scheme* structure on `Pic⁰` (representability = the Jacobian, holes 2–9) is Wall δ,
>   untouched. See `docs/SHARED_FOUNDATION_ROUTE_2026_06_13.md`.
> - **`main` is now @ `2f2692b`** (was `07c0766` at round-3 start). This session pushed I.1a piece (III)
>   bricks 2–3 (above) and **integrated `tower/jacobian-r2`** (+1: Tower B `tensorPowMulEquiv`,
>   `A^⊗d ⊗ A^⊗e ≃ₐ A^⊗(d+e)`, `Submission/Jacobian/TensorPowerAdd.lean`); integration gate green
>   (8354 jobs, vacuity 0/39). Integrator queue clear as of push; `tower/abelian-variety-r2` 0-ahead.
> - **(prior) Just integrated:** `tower/stack-II-serre` (+5: Tower-A smooth⇒regular for rel-dim-1 curves +
>   scalar-transport; Front-B Mayer-Vietoris LES computing `H1 C` + `coeffSheaf ≅ k[⊤]`) → `main` @
>   `07c0766`, gate green (8353 jobs, vacuity 0).
> - **Integrator duty:** `git fetch`; for any `tower/*` branch with commits ahead of `main`, merge into
>   an integration branch off `main`, run the solo gate (`~/.claude/bin/lakelock lake build` +
>   `python3 scripts/lean_vacuity_lint.py Submission.lean Submission/ --max-findings 0`), confirm
>   `origin/main` unmoved, fast-forward + push, delete the integration branch.

> **(superseded) ROUND 2 ENTRY (2026-06-13):** integrator + Tower-A, `main` @ `b6b2062`. Tower B/C
> on `tower/jacobian-r2`/`tower/abelian-variety-r2`.

> **ROUND-2 PROGRESS (2026-06-13, `main` @ `5d3a8ed`):** Tower-A landed `regular ⇒ domain` in
> **ALL dimensions** (Stacks 00NP) — `Submission/Cohomology/RegularLocalDomainGeneral.lean`
> (green, axiom-clean, vacuity 0, full build 8335 jobs, pushed). Closes the `regular ⇒ domain`
> leaf of Wall 2. **Next reachable Tower-A leaf** = `smooth ⇒ regular local`, which needs ONE of:
> (a) finite-type-over-field **dimension formula** (`dim` standard-smooth local k-alg = rel dim),
> or (b) **residue-field cotangent sequence** `finrank_κ(𝔪/𝔪²) = rel dim`. Both compile-verified
> absent at the pin. See `OPEN.md` §"Tower-A foundation (round 2)" +
> `docs/ROUTE_RESEARCH_2026_06_13.md` §"TOWER A — round-2 brick" + LEAP_QUEUE §5.
>
> **I.1a IN PROGRESS (Bryan: "Build I.1a now", 2026-06-13).** Discharging
> `(sheafificationW J R₀).IsMonoidal` = build the **internal hom of presheaves of modules over a
> varying ring** + sheaf-preservation, then port `whiskerLeft`/`whiskerRight`. File
> `Submission/Cohomology/PresheafOfModulesInternalHom.lean`. **✅ Piece (I) DONE** (W = Bousfield
> local class). **✅ Piece (II) OBJECT DONE (`main` @ `1a6d06e`, pushed, full build 8341 jobs,
> vacuity 0, axioms clean):** `internalHomObj F H X : ModuleCat (R₀.obj X)` = `[F,H](X)` — the
> R₀(X)-module of slice-morphisms `(restrict X).obj F ⟶ (restrict X).obj H`, with the full
> `Module (R₀.obj X)` instance (`internalSMulApp`/`internalHomSMul`/`internalHomModule`). **The
> instance-diamond WALL FELL** (it was THE blocker): scaling a `ModuleCat (R₀'.obj _)` morphism by a
> ring element fails synthesis (morphism-scaling needs `SMulCommClass`/`Linear` over the RingCat
> carrier, not found), but *element*-scaling via mathlib's `Module (R₀.obj X) (M.obj X)` succeeds —
> so build the scaled morphism **element-wise as a LinearMap over the CommRingCat carrier
> `R₀.obj (op W.left)`** (carrier discipline). Naturality reduces to scalar restriction-compat (Over
> triangle) + `φ.naturality` + `H` restriction semilinearity.
> **✅ RESTRICTION MAP DONE (2026-06-14, `main` @ `4e5b000`): the carrier diamond is CRACKED.**
> `internalHomMapHom f : internalHomObj X ⟶ restrictScalars (R₀.map f) (internalHomObj Y)` (the map
> field of `[F,H]`), full build green, vacuity 0, axioms clean. The restriction is FREE from
> `pushforward₀` functoriality (`internalHomMap f φ := (pushforward₀ (Over.map f.unop) _).map φ`, `rfl`
> typed); semilinearity by the object's scalar-compat. **The diamond crack (reuse this):** the PMod
> `map` field's `restrictScalars` is over the RingCat presheaf but `internalHomObj` is over the
> CommRingCat carrier — resolve with (i) `ModuleCat.semilinearMapAddEquiv (R₀.map f).hom M N` (semilinear
> map → restrictScalars morphism, avoids carrier-collapse) + (ii) `restrictScalars` written over
> `(R₀.map f).hom` (reduced CommRingCat hom, defeq to `((R₀⋙forget₂).map f).hom`, keeps the reduced
> carrier where instances live).
> **✅ PRESHEAF ASSEMBLED — `internalHom : PresheafOfModules.{max u u' v'} R₀'` DONE (2026-06-14):**
> `obj := internalHomObj`, `map := internalHomMapHom`, with `map_id`/`map_comp`. Full build green
> (8342 jobs), vacuity 0, axioms clean (`[propext, Classical.choice, Quot.sound]`). **`[F,H]` is now a
> presheaf of modules — piece (II) is COMPLETE.** Technique that worked (reuse for piece III): the
> presheaf laws factor through two element-level helper lemmas on the underlying slice-morphisms —
> `internalHomMap_id`/`internalHomMap_comp` — each closed by
> `simpa [Over.mapId/mapComp, PresheafOfModules.pushforward₀] using PresheafOfModules.naturality_apply
> φ ((Over.mapId/mapComp …).hom.app V.unop).op z` (the `presheafHom` iso-naturality pattern, element
> level). **Two traps found & solved:** (a) you MUST unfold `PresheafOfModules.pushforward₀` (with the
> namespace! bare `pushforward₀` is unknown) so the `((restrict X).obj F).map ι` wrappers reduce via
> `pushforward₀_obj_map` → `F.map 𝟙 = 𝟙`; (b) `ModuleCat.Hom.hom` is an *abbrev* for
> `ConcreteCategory.hom`, so `naturality_apply` (coe form) and the `ModuleCat.hom_ext`+`LinearMap.ext`
> goal (`.hom` form) differ only by an abbrev — `simpa`'s final `exact` bridges them, no manual coe
> rewriting needed. The structure fields then close by `rw [internalHomMapHom_hom_apply,
> internalHomMap_id/comp]; rfl` — the `restrictScalarsId'/Comp'App.inv` coherence isos are
> identity-on-carrier by `rfl` (the carrier-diamond means the App-level simp lemmas DON'T fire, but
> plain `rfl` at default transparency does).
> **(b) tensor-hom adjunction (`Closed F`) — IN PROGRESS.** PMod's monoidal structure is the
> POINTWISE tensor `(F ⊗ G).obj X = F.obj X ⊗ G.obj X` (`Presheaf/Monoidal.lean`), so `internalHom`
> (slice-morphisms = the module `presheafHom`) is exactly its right adjoint — the adjunction is the
> cartesian-closed-style presheaf curry/uncurry. **✅ rightAdj BUILT (2026-06-14, `main` @ `4c48e81`,
> 8344 jobs, vacuity 0, axioms clean):** `internalHomFunctor F : PMod ⥤ PMod` (`internalHom F` made
> functorial in `H`; `internalHomMapSnd` = postcompose slice-morphisms with `(restrict X).map ψ`).
> **Lessons baked in (reuse for the homEquiv):** (1) the carrier diamond bites when applying a
> morphism's `.app W` to a CommRing scalar — `map_smul` won't fire on `((restrict X).map ψ).app W`;
> express it in the REDUCED form `ψ.app (op W.unop.left)` (= it by `rfl`, the `appAt` discipline) and
> `map_smul`/`rw` work. (2) `Functor.map_id`/`map_comp` resolve to the *Monad* `Functor` class — use
> `CategoryTheory.Functor.map_id`/`map_comp`. (3) when a simp lemma won't fire because a bound var's
> type is defeq-but-not-syntactic (`φ : ↑((internalHom F H).obj X)` vs `internalHomObj F H X`), state
> the defeq-reduced goal with `show` and bypass simp-matching.
> **✅ COUNIT BUILT (2026-06-14, `main` @ `4722942`, 8345 jobs, vacuity 0, axioms clean):** new
> single-universe file `Submission/Cohomology/PresheafOfModulesClosed.lean` (namespace
> `InternalHomClosed`, `C : Type u`/`Category.{u}`). `internalHomEval F H : F ⊗ internalHom F H ⟶ H` =
> the evaluation/counit: at `X`, `f' ⊗ φ ↦ φ(X)(f')` (`evalAppMap` via `ModuleCat.…tensorLift`).
> **CRITICAL idioms discovered here (reuse for unit + the rest):** (a) **PMod's tensor lives over the
> *CommRingCat* carrier `R₀.obj X`, NOT the RingCat `R₀'(X)`** (which isn't commutative ⇒ no
> `MonoidalCategoryStruct`); every tensor-touching def needs `set_option
> backward.isDefEq.respectTransparency false in` so `MonoidalCategoryStruct (ModuleCat (R₀'(X)))`
> resolves via the `CommRing`-through-`forget₂` defeq. (b) The tensor factor must be written
> `(internalHom F H).obj X` (structure carrier), not `internalHomObj F H X`. (c) `tensorLift` h₃ (add
> in 2nd arg) closes by `rfl` (`PresheafOfModules.add_app` is `rfl`); `internalSMulApp_hom_apply` needs
> `erw` (φ-carrier defeq); the `R₀(𝟙)`-scalar collapses via `R₀.map_id`. (d) Naturality-in-X reduces
> by `tensor_ext` + `PresheafOfModules.naturality_apply φ (Over.homMk f.unop _).op f'` then
> `exact key` (defeq bridges `((restrict X)·).map θ.op = ·.map f`); needed simp = just
> `[ModuleCat.comp_apply, restrictScalars.map_apply, evalAppMap_tmul]`.
> **✅ UNIT + `Closed F` DONE (2026-06-14, single-file green ~7s, vacuity 0, axioms clean
> `[propext, Classical.choice, Quot.sound]`):** `PresheafOfModulesClosed.lean` now ends with
> `instance closedObj : Closed F := { rightAdj := internalHomFunctor F, adj := internalHomAdjunction F }`.
> Built (in order): `coevAppHom X` (`semilinearMapAddEquiv (RingHom.id (R₀.obj X))` — the *identity*
> ring hom, so `restrictScalars`-codomain is defeq to the structure obj and `internalHomCoev.app := coevAppHom`
> typechecks directly; `map_smul'` via `coevSliceApp_hom_apply` + `← TensorProduct.tmul_smul` + `congr 1`
> + `erw [PresheafOfModules.map_smul]` to keep the CommRingCat scalar native to the tensor) → `internalHomCoev`
> (naturality-in-X = `← map_comp_apply` then **`congr 1` closes outright**) → `internalHomEvalNat`
> (counit NatTrans-in-H, naturality `rfl` after `hom_ext`+`tensor_ext`) → `internalHomCoevNat` (unit
> NatTrans-in-G, naturality = `whiskerLeft_apply` + `(naturality_apply γ …).symm`) → `internalHomAdjunction`
> (built **directly as `Adjunction`**, not `mkOfUnitCounit` — its `left/right_triangle_components` fields
> ARE per-component). **Triangle lessons (reuse for piece III):** *left* reduces on `f'⊗g` to `G.map (𝟙 X) g = g`
> — close with `show (G.map (𝟙 X)).hom g = g; rw [PresheafOfModules.map_id]; rfl` (the `(unop topSlice).hom.op = 𝟙 X`
> retype is defeq via `show`); *right* reduces on `φ` to the `Over.map (𝟙)`/`topSlice` reindex `op (Over.mk (𝟙≫h)) = V`
> — close via `erw [coevSliceApp_hom_apply, evalAppMap_tmul, internalHomMapHom_hom_apply, internalHomMap_app]`
> then an explicit object-eq `hobj` (peel `id_comp`) **rewritten through the dependent `φ.app` position with
> `rw [eq_of_heq (congr_arg_heq φ.app hobj)]`** (plain `rw`/`simp`/`▸`/`convert` all fail the motive; the
> `congr_arg_heq`→`eq_of_heq` morphism-equality is motive-safe because it rewrites a *fixed-type* morphism).
> **NEXT = piece (III), the ONLY remaining I.1a content — a genuine multi-session theorem
> (Stacks 17.16; mathlib lacks any module-sheaf internal hom, confirmed 2026-06-14). ROUTE DOC
> WRITTEN: `docs/PIECE_III_SHEAF_PRESERVATION_ROUTE_2026_06_14.md`** — read it first. Summary: the
> cheap shortcuts are DEAD (`toPresheaf` is NOT monoidal — module ⊗ ≠ ℤ ⊗; `Presheaf.IsSheaf.hom`
> only gives the *type* hom, not the R₀-linear sub-object). Two live routes: **(A)** mirror
> `presheafHom_isSheafFor` (`Sites/SheafHom.lean:172`) threading R₀-linearity through the limit-lift;
> **(B)** `(internalHom F H).presheaf ≅ equalizer(presheafHom(F,H) ⇉ presheafHom(R₀⊙F,H))` then
> `Presheaf.isSheaf_of_isLimit` (`Sites/Limits.lean:136`, mathlib-backed) — the load-bearing step is
> the iso "PMod-morphism ⟺ linear nat. transf." Once (III) lands, the whiskerLeft/Right/IsMonoidal
> **port is short (~40-60 LOC)** and uses ONLY the already-built `closedObj` (its `Adjunction.homEquiv`
> naturality is free) + `sheafificationW_eq_isLocal`/`bijective_precomp` (piece I) + the PMod braiding
> — see the route doc's "short remainder" §. Full detail: that doc; `LEAP_QUEUE §6`.
>
> **PLAN DOCS (read these to drive):** the A-vs-B route leap is **deferred — build the shared
> foundation first** (`docs/SHARED_FOUNDATION_ROUTE_2026_06_13.md`: Stack I sheaves→Pic→ample,
> Stack II cohomology→Serre→RR; bottom brick I.1 = `SheafOfModules` monoidal, **scaffold DONE**,
> reduced to I.1a = `W.IsMonoidal` = sheafification⊗tensor = Stacks 17.16, now IN PROGRESS).
> Top-down roadmap from the COMPLETED Riemann-surface challenge (rkirov, solved end-to-end):
> `docs/ROADMAP_FROM_COMPLETED_CHALLENGE_2026_06_13.md` — confirms the 9-hole shape + downstream
> ordering (holes 3,4,5,6 fall out of hole 2's construction), but is **silent at hole 2** (the RS
> solution used the analytic `ℂᵍ/Λ` shortcut; no algebraic analogue — the construction is the gate).

## 🟢 MANDATE: build the challenge to completion — mathlib work is IN-SCOPE
Goal = comparator pass (all 9 holes), not banking bricks. Building absent mathlib infrastructure on
the critical path — **Serre finiteness of coherent cohomology, Riemann–Roch, regular-local-ring
theory, the curve's affine cover** — **is first-class. Build it relentlessly, brick by brick.** LOC
is not a ceiling (the old "stop at 5k / convert to PR" check is RETIRED). Only hard limits: no
`sorry`/`axiom`, vacuity 0, byte-compatible statements, and the `lakelock` panic rules.

## Your two jobs
**(1) Tower A — coherent cohomology → Serre finiteness (holes 1, 4).** Round 1 built (on `main`):
`Submission/Cohomology/RegularLocalDomain.lean` (regular local **dim ≤ 1 ⇒ reduced**, the
`tᵏ·unit` decomposition) + `LinearH0.lean` (Adjunction linearity lemmas). **Next bricks:**
- **smooth `k`-algebra local ⇒ regular of dim ≤ 1**: connect `StandardSmoothCotangent` (finrank
  cotangent = rel dim, present) to `IsRegularLocalRing.iff_finrank_cotangentSpace` (present); the
  sub-gap is **Krull-dim-of-smooth = rel dim** — build it (mathlib in-scope; `KrullsHeightTheorem`
  is present to build on).
- then **smooth scheme over `k` ⇒ all stalks regular ⇒ reduced ⇒ `IsReduced C.left` ⇒ `IsIntegral`
  ⇒ `Γ(C,⊤)` finite over `k`** (`finite_appTop_of_universallyClosed`) **= h⁰ finiteness** (the
  whole chain except smooth⇒reduced already infers — see `docs/ROUTE_RESEARCH_2026_06_13.md`
  §"TOWER A … obstruction map").
- **Wall 1 (the H¹ goal): `FiniteDimensional k (H1 C)` = Serre finiteness** via the local-to-global
  / derived↔Čech comparison (bridges the submission's sheaf-`Ext` to the present `ModuleCat.finite_ext`).
  Build it — this certifies the genus and is the real Tower-A target.
- **Riemann–Roch** (genus = h¹(𝒪)) — feeds Tower B's "AJ birational at d=g".

**(2) Integrator.** When B or C reports a green branch: `git fetch`, merge their `tower/*-r2` into an
integration branch off `main`, run the **solo merge gate** `~/.claude/bin/lakelock lake build` +
`python3 scripts/lean_vacuity_lint.py Submission.lean Submission/ --max-findings 0`, then push `main`.
Towers rebase onto the new `main`. (Round-1 protocol — see PARALLEL_PLAN "Integration protocol".)

Build via `~/.claude/bin/lakelock lake env lean FILE` / `lakelock lake build` (mutex + throttle; the
PreToolUse hook denies raw lake). Tower A files under `Submission/Cohomology/…`.

---

# NEXT SESSION — continuous-driving entry

**Working model (not a loop).** One continuous Claude session drives as far as
its context allows — chaining chips with the warm local cache (`lake env lean`
~5–8s) WITHOUT re-reading everything per chip — then checkpoints here and a
fresh session continues. The unit is "a context-window of continuous work
(~thousands of LOC)", not "one cold chip per wake-up". The cron loop was
retired 2026-06-13 (cold-start re-orientation tax + can't carry the route +
stacked/wedged); see git history if curious.

On entry: skim `OPEN.md`, this file's "current segment", `CHIP_GATES.md`,
`DEVELOPMENT.md`, and the route doc's tail — then DRIVE. Don't re-audit.

## Build target (reframed 2026-06-13): GO — build the coherent-cohomology stack

The earlier "NO-GO" was an over-escalation. Per "mathlib work is in scope",
the missing coherent-cohomology infrastructure is THE WORK, not a blocker.
The genus (hole 4) needs `FiniteDimensional k H¹(C, 𝒪_C)`; we build up to it.

**Substrate that EXISTS at the pin** (use it, don't reinvent — Gate 6):
- `CategoryTheory/Sites/GlobalSections.lean`: `Sheaf.Γ J A : Sheaf J A ⥤ A`
  general global sections (right adjoint of constant sheaf), exists when
  `A` has `Cᵒᵖ`-limits — so for `A = ModuleCat k`. ✓
- `ModuleCat k`: Grothendieck-abelian, enough injectives
  (`ModuleCat/EnoughInjectives.lean`, `ModuleCat/AB.lean`). ✓
- `CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean`: Grothendieck-
  abelian ⇒ `HasExt`. ✓
- `Sheaf.H` pattern (`Sites/SheafCohomology/Basic.lean`): cohomology as
  `Ext(constantSheaf (unit), F, n)` — but hard-wired to `AddCommGrpCat`.
- `PresheafOfModules`/`SheafOfModules` + `restrictScalars`,
  `Submission/StructureSheafModule.lean` (`underToModuleCat`), and the M1a
  Čech layer `Submission/CechModuleCat.lean`.

**Build order (each ~a segment):**
1. **`Submission/SheafCohomologyModuleCat.lean` — `Hⁿ` valued in `ModuleCat k`.**
   Mirror `Sheaf.H` but coefficient category `ModuleCat k`:
   `Hⁿ(F) := Ext (constantSheaf J (ModuleCat k)).obj (unit) F n`, taken in
   `Sheaf J (ModuleCat k)`. NEEDS `HasExt (Sheaf J (ModuleCat k))` — establish
   it (is `Sheaf J (ModuleCat k)` Grothendieck-abelian? `Sheaf.H` takes the
   AddCommGrp analogue as a *hypothesis*, so we likely must build/assume it
   too — first investigate whether the sheaf-of-Grothendieck-abelian category
   has an `IsGrothendieckAbelian` instance; if not, that sub-lemma is the
   first real content). DONE WHEN: `Hⁿ` def + `H⁰ ≅ Γ` compiling.
2. Present `𝒪_C` as a sheaf of `k`-modules (`underToModuleCat` ∘ structure
   sheaf over the structure morphism), feed it to (1) → `H¹(C, 𝒪_C)` as a
   `k`-module. (This is the fork-B path; sidesteps the affine-cover gap.)
3. **The hard wall: `FiniteDimensional k (H¹ C 𝒪_C)` (Serre finiteness).**
   No mathlib foundation — this is the major sub-arc (coherent sheaves +
   proper-pushforward finiteness). Scope it as its own route doc when reached.

## Current segment

**Segment 1 = build target step 1** (`Hⁿ` valued in `ModuleCat k`) — ✅ **DONE
2026-06-13**, `Submission/SheafCohomologyModuleCat.lean`, sorry/axiom-clean,
vacuity-lint 0, full `lake build` green (8319 jobs). See `OPEN.md` "Segment 1
DONE" for the decls (`coeffSheaf`, `H`, `HZeroAddEquivΓ`).

**The gating question was WRONG.** mathlib DOES hand us `HasExt` for
`Sheaf J (ModuleCat k)`: the `IsGrothendieckAbelian (Sheaf J A)` instance is at
the pin (`Abelian/GrothendieckAxioms/Sheaf.lean`), so `HasExt`, `Linear k`, and
`Module k (Ext …)` all resolve automatically. (The earlier "no such instance"
note was a GitHub-pin survey before the local cache was warm — Gate 6 caught it.)
Segment 1 was a few hours of *assembly*, not the feared homological-algebra build.

**Segment 2 (build target step 2) = ✅ DONE 2026-06-13**,
`Submission/StructureSheafCohomology.lean`. `H¹(C, 𝒪_C)` as a `k`-module +
**hole 1 (`genus`) filled** (`Submission.genus = Module.finrank k (H1 C)`,
sig byte-compatible, sorry/axiom-clean). See `OPEN.md` "Segment 2 DONE".

The handoff's feared blockers evaporated: the curve's *opens site*
(`Opens.grothendieckTopology C.left`) is `SmallCategory` and
`HasSheafify (Opens.gt) (ModuleCat k)` **resolves automatically** — so no
`EssentiallySmall` bridge and no `HasSheafify` discharge were needed. The sheaf
condition transports from `C.left.IsSheaf` for free (defeq underlying `Type`-presheaf
+ `forget (ModuleCat k)` reflects limits). The structure-sheaf `k`-algebra lift goes
through Segment-1b's `underToModuleCat`.

**Segment 3 = THE WALL (current segment):** `FiniteDimensional k (H1 C)` — Serre
finiteness for the proper curve. `H1 C` is *type-correct* for it (a `k`-module), but
mathlib at the pin has **no** quasi-coherent/coherent sheaves, no proper-pushforward
finiteness, no Serre finiteness to stand on. This is the major sub-arc the route doc
flagged — needs its own route doc when started. Until it lands, `genus C`'s *value* is
the `finrank` junk-`0` on the (unproven-finite) `H¹` rather than the honest genus; the
def is filled but the value is not yet certified.

## ⚠️ Scope reality (READ before committing more sessions — 2026-06-13)

The cohomology stack (Segments 1–3) serves **only hole 1 (`genus`)**. Two facts:
- `genus C : ℕ` is a bare `def` with **no required equation**; hole 4 only needs
  `SmoothOfRelativeDimension (genus C) (Jacobian C).hom`. The math pins `genus` =
  dim of the Albanese (forced by hole 9's universal property), but nothing forces
  the *formalization* to route genus through `H¹`.
- Holes 2,3,5,6,7,8,9 = constructing `Jacobian C` (= Pic⁰) as an abelian variety
  with group structure, properness, geometric irreducibility, the Abel–Jacobi
  map, and the **universal property of the Albanese**. This is FGA-grade and has
  **zero mathlib foundation** (no Picard scheme, no abelian varieties, no
  Albanese, no representability of Pic). It is the overwhelming bulk of the arc.

So even a *perfect* Segment 1–3 build closes at most hole 1 and contributes to
hole 4's statement. **The GO decision should be re-weighed against this**: the arc
is reachable only after the Jacobian-representability program, which dwarfs the
cohomology stack. Forks for Bryan unchanged from the route doc's NO-GO verdict
((I) commit to the infra program / (II) land bounded pieces upstream as mathlib
PRs / (III) shelve) — but now with Segment 1 already a clean, upstreamable piece
under fork (II). Per `feedback_obstruction_then_human_leap`, this is stated for
the human leap, not ground past solo.

## Arc DONE WHEN

A submission accepted by the lean-eval comparator for
`jacobian_challenge_alggeo` (all 9 holes, sorry-free, axiom-free) + maintainer
audit. (Long arc; the genus/finiteness sub-arc is the bulk.)
