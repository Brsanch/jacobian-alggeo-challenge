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

**Segment 1 = build target step 1** (`Hⁿ` valued in `ModuleCat k`), file
`Submission/SheafCohomologyModuleCat.lean`.

**Gating question RESOLVED (2026-06-13):** mathlib does NOT hand us `HasExt`
for sheaf categories — `Sheaf.H` (`Sites/SheafCohomology/Basic.lean:54-55`)
takes `[HasSheafify J AddCommGrpCat]` AND `[HasExt (Sheaf J AddCommGrpCat)]` as
**instance hypotheses**, and there is no `IsGrothendieckAbelian (Sheaf J A)`
instance at the pin. So segment 1's first concrete task is to establish
`HasExt (Sheaf J (ModuleCat.{w} k))` — mathematically true (sheaves valued in a
Grothendieck-abelian category over a site with sheafification form a
Grothendieck-abelian category ⇒ `HasExt` via
`Abelian/GrothendieckCategory/HasExt.lean`), but it needs:
`HasSheafify J (ModuleCat k)` + transferring `IsGrothendieckAbelian` from
`ModuleCat k` to `Sheaf J (ModuleCat k)` (generator + AB5; check
`Sites/Abelian.lean`, `Sites/LeftExact.lean`, the `GrothendieckCategory`
files). This Grothendieck-abelian-of-sheaves lemma is itself likely a
sub-segment — it is the real first piece of content, not boilerplate.

Then: `Hⁿ(F) := Ext (constantSheaf J (ModuleCat k)).obj (𝟭_k) F n` mirroring
`Sheaf.H`, with `H⁰ ≅ Γ` from `Sheaf.Γ`/`constantSheafΓAdj`. DONE WHEN: those
compile sorry-free.

⚠️ This is hard homological-algebra infra — drive it with a FRESH full context
window (that is the "clear context and keep going" step). Starting it from an
already-loaded session is the anti-pattern the segment model avoids.

## Arc DONE WHEN

A submission accepted by the lean-eval comparator for
`jacobian_challenge_alggeo` (all 9 holes, sorry-free, axiom-free) + maintainer
audit. (Long arc; the genus/finiteness sub-arc is the bulk.)
