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

**Segment 2 (build target step 2) = next.** Present `𝒪_C` as a sheaf of
`k`-modules and feed it to `H` to get `H¹(C, 𝒪_C)` as a `k`-module. Substrate:
`Submission/StructureSheafModule.lean` (`underToModuleCat`, `Under R ⥤ ModuleCat R`)
+ `AlgebraicGeometry/Sites/SmallAffineZariski.lean` (`Scheme.AffineZariskiSite`,
`sheafEquiv`). The universe/`HasSheafify J (ModuleCat k)` discharge for the
actual curve's site is the real work here (the abstract module carries
`[HasSheafify …]` as a hypothesis, mathlib-`Sheaf.H`-style; instantiation must
supply it — the site is `EssentiallySmall`, so the bridge is
`Sheaf.isGrothendieckAbelian_of_essentiallySmall`, not the `SmallCategory`
instance Segment 1 used).

**Segment 3 = the wall:** `FiniteDimensional k (H¹ C 𝒪_C)` (Serre finiteness),
no mathlib foundation — its own major sub-arc.

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
