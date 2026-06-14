# 🟢 ROUND 2 ENTRY (2026-06-13) — INTEGRATOR + TOWER A, in this canonical checkout

You are the fresh integrator + Tower-A session (replacing round 1), on `main` @ `b6b2062`
(all three towers' round-1 foundation integrated + pushed). Two parallel sessions run Tower B
(`…/jacobian-alggeo-parallel/jacobian`, branch `tower/jacobian-r2`) and Tower C
(`…/abvar`, branch `tower/abelian-variety-r2`). Control room: `…/jacobian-alggeo-parallel/PARALLEL_PLAN.md`.

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
> **NEXT = piece (II) PRESHEAF + adjunction. The restriction map was SCOUTED 2026-06-14 (validated in
> probe, not committed — blocked on a carrier diamond):** the restriction map is FREE from
> `pushforward₀` functoriality — `internalHomMap f φ := (pushforward₀ (Over.map f.unop) _).map φ` is
> `rfl`-typed as `(restrict Y).obj F ⟶ (restrict Y).obj H` (so naturality + additivity are free); the
> presheaf lives in `PresheafOfModules.{max u u' v'}` (the Hom-set is universe-big; collapses to `.{u}`
> when `u'≤u, v'≤u`, the port's setting). **WALL:** the PMod `map` field's `restrictScalars` is over the
> RingCat presheaf, so assembling hits a CommRingCat↔RingCat Ring-instance diamond — `internalHomObj`
> over `R₀.obj X` (CommRingCat, committed) fails the restrictScalars synth; over `(R₀⋙forget₂).obj X`
> (RingCat) the restrictScalars works + axioms survive (with `erw [map_mul]`/`erw [map_add]`) but
> `ModuleCat.of` hits a Ring-instance diamond. **Fix:** explicit-instance/`letI` navigation like
> mathlib's `pushforward₀_obj` (`@LinearMap.ext … (_) (_)`), or package the whole presheaf via
> `pushforward₀` pseudo-functoriality (`pushforwardId`/`pushforwardComp` + `Over.mapId`/`mapComp`,
> mirroring `presheafHom`) so the diamond rides mathlib's workarounds. Then (b) tensor-hom adjunction
> (`Closed F`), piece (III) sheaf-preservation, ~30-line port. Full detail + every handle:
> `docs/ROUTE_RESEARCH_2026_06_13.md` §"I.1a BUILD" piece (II) "NEXT"; `LEAP_QUEUE §6`.
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
