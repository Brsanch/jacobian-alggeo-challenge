# Open items — jacobian-alggeo-challenge

> **Before any new Lean work: read `CHIP_GATES.md` (repo root)** — vacuity
> lint gate (mechanical, baseline-ratcheted) + the anti-paraphrase gates —
> and `DEVELOPMENT.md` (panic-safe build rules, eval submission mechanics).

## Approach (reframed 2026-06-13): GO — continuous-driving build of the coherent-cohomology stack

The genus (hole 4) needs `FiniteDimensional k H¹(C,𝒪_C)` = Serre finiteness;
mathlib at the pin has no quasi-coherent/coherent sheaves or scheme cohomology.
The earlier "NO-GO, escalate" framing was an over-escalation: per "mathlib work
is in scope", this infrastructure IS the work. We build it via continuous Claude
segments (see `NEXT_SESSION.md` working model + build order), NOT the retired
cron loop. Abstract substrate that exists (`Sheaf.Γ` general global sections,
`ModuleCat k` Grothendieck-abelian, Grothendieck⇒HasExt) makes the fork-B
cohomology route viable; finiteness (step 3) is the major sub-arc. All 9 holes
remain OPEN. Detail: `docs/ROUTE_RESEARCH_2026_06_13.md`.

## (pre-verdict) current state (2026-06-13: scaffold, all 9 holes OPEN)

Target: the official lean-eval problem
[`jacobian_challenge_alggeo`](https://lean-lang.org/eval/problems/jacobian_challenge_alggeo/)
(Christian Merten's algebraic-geometry analogue of the Buzzard Jacobian
challenge; the diffgeo variant was solved by rkirov/jacobian-claude
2026-06-11). DONE WHEN (arc): a submission accepted by the lean-eval
comparator and audited by the maintainer. Status board: Kim Morrison's
[Manifold market](https://manifold.markets/kimem/when-will-the-jacobian-challenge-be).

| # | Hole | Kind | Status |
|---|------|------|--------|
| 1 | `genus` | def | OPEN |
| 2 | `Jacobian` | def | OPEN |
| 3 | `Jacobian.instGrpObj` | def | OPEN |
| 4 | `Jacobian.smoothOfRelativeDimension_genus` | theorem | OPEN |
| 5 | `Jacobian.instIsProper` | theorem | OPEN |
| 6 | `Jacobian.instGeometricallyIrreducible` | theorem | OPEN |
| 7 | `Jacobian.ofCurve` | def | OPEN |
| 8 | `Jacobian.comp_ofCurve` | theorem | OPEN |
| 9 | `Jacobian.exists_unique_ofCurve_comp` | theorem | OPEN |

Current phase: **M1 (coherent cohomology canary)** — M0 done (scaffold + CI
green + manifest, `3a3066d`). See `docs/ROUTE_RESEARCH_2026_06_13.md`.

### ✅ Segment 1 DONE (2026-06-13, `Submission/SheafCohomologyModuleCat.lean`, full-build green)

Derived-functor sheaf cohomology valued in `ModuleCat k` (build-target step 1,
the fork-B route that sidesteps the M1b explicit-cover gap). Compiles sorry-free
+ axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only); vacuity-lint 0;
throttled full `lake build` green (8319 jobs, exit 0).
- `coeffSheaf J k : Sheaf J (ModuleCat k)` — constant sheaf with value `k`.
- `H J k n F := Ext (coeffSheaf J k) F n` — degree-`n` cohomology, a **`k`-module**
  by `Ext.instModule` (`Sheaf J (ModuleCat k)` is `k`-linear), so
  `FiniteDimensional k (H J k 1 F)` is type-correct.
- `HZeroAddEquivΓ : H J k 0 F ≃+ (Sheaf.Γ J (ModuleCat k)).obj F` — **degree-0
  cohomology = global sections** (as abelian groups). This is the `ModuleCat k`
  analogue of the `H⁰ ≅ Γ` that mathlib's `Sheaf.H` only lists as a *TODO*. New
  supporting lemma: `Functor.const_additive` (additivity of `Functor.const Cᵒᵖ`,
  missing from mathlib).

**Two material corrections to the route doc / NEXT_SESSION (Gate-6 survey, warm cache):**
1. **The feared "first real content" is already in mathlib.** NEXT_SESSION said
   there is *no* `IsGrothendieckAbelian (Sheaf J A)` instance at the pin and that
   building it (⇒ `HasExt`) was segment 1's first task. False: the instance IS at
   the pin (`Abelian/GrothendieckAxioms/Sheaf.lean`), so `HasExt (Sheaf J (ModuleCat k))`,
   `Linear k (Sheaf J (ModuleCat k))`, and `Module k (Ext …)` all resolve
   automatically. Segment 1 was assembly, not foundation-building. (The earlier
   survey was at the GitHub pin before the local cache was warm.)
2. **The genus hole has NO required equation.** `genus C : ℕ` (hole 1) is a bare
   `def`; hole 4 only needs `SmoothOfRelativeDimension (genus C) (Jacobian C).hom`.
   So genus is pinned by the *math* (= dim of the Albanese, forced via hole 9's
   universal property) but the *formalization* never forces `genus := dim_k H¹`.
   ⇒ **the cohomology stack serves only hole 1.** Even a complete coherent-
   cohomology + Serre-finiteness build leaves holes 2,3,5,6,7,8,9 — the Jacobian/
   Albanese construction with its universal property — untouched. Those are the
   FGA-grade wall with zero mathlib foundation (no Picard scheme, no abelian
   varieties, no Albanese). **The arc's true bulk is the Jacobian construction,
   not the cohomology stack.** This is the decisive-regime-reachability datum for
   Bryan's scope decision (see `NEXT_SESSION.md` "Scope reality").

M1 declaration-level mathlib inventory + k-module **encoding decision** done
in loop run #1 (2026-06-13): `H¹ C 𝒪_C` will be the degree-1 homology of the
two-affine-cover Čech complex **in `ModuleCat k`** (`cechComplexFunctor` is
preadditive-generic; the abelian-group `Sheaf.H` can't carry the needed
k-module structure). M1 split into:

| M1 sub | content | status |
|---|---|---|
| M1a | abstract Čech complex in `ModuleCat k` + `cechH` def + H⁰≅ker(d⁰) + d⁰=δ⁰−δ¹ + **H⁰≅equalizer(δ⁰,δ¹)** | **DONE (abstract layer)** (`55532a9`, `681626a`, `92a91be`) — def layer + cocycle lemma + first unfold (`d⁰=δ⁰−δ¹`) + **equalizer iso** all CI-green. Coordinate-level identification of the cofaces as `Pi.lift`-of-`P.map` restrictions deferred into M1b (where ι=Fin 2 / 𝒪_C make the restrictions explicit). |
| M1b | the curve's two-affine cover + **concrete restriction/intersection maps** (incl. the coface coordinate-unfold via `evalOp`/`mapPower` `@[simps]`) + wire `𝒪_C` as `ModuleCat k`-presheaf | OPEN |
| M1c | `FiniteDimensional k (H1 C 𝒪_C)` (Serre finiteness; go/no-go datum) | OPEN |

**M1a progress (loop run #2, 2026-06-13, `Submission/CechModuleCat.lean`, CI-green, merged `55532a9`):**
- `cechComplexMod (U : ι → C) : (Cᵒᵖ ⥤ ModuleCat k) ⥤ CochainComplex (ModuleCat k) ℕ` — `cechComplexFunctor` specialized to the preadditive target `ModuleCat.{w} k` with `ι : Type w`. **This compiles → the route-doc encoding decision is sound** (universe/instance resolution works at `A := ModuleCat.{w} k`, `ι : Type w`).
- `cechH (U) (n) : (Cᵒᵖ ⥤ ModuleCat k) ⥤ ModuleCat k` := `cechComplexMod U ⋙ homologyFunctor _ _ n`. So `FiniteDimensional k _` (M1c) is type-correct on `(cechH U n).obj P`.
- `cechHZeroIsoKernel : (cechH U 0).obj P ≅ kernel ((cechComplexMod U).obj P).d 0 1` — Čech H⁰ ≅ kernel of the first Čech coboundary (cocycle description; via `CochainComplex.isoHomologyπ₀` + `cyclesIsKernel`).
- **First equalizer-unfold DONE (loop run #3, 2026-06-13, `681626a`, CI-green run `27454466919`):**
  - `cechCosimpl (U) (P) : CosimplicialObject (ModuleCat k)` := `(FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk _ U).cech).obj P`. By construction `(cechComplexMod U).obj P = alternatingCofaceMapComplex.obj (cechCosimpl U P)` (defeq).
  - `cechComplexMod_d_zero_one : ((cechComplexMod U).obj P).d 0 1 = (cechCosimpl U P).δ 0 − (cechCosimpl U P).δ 1`. Proof: `show` to `AlternatingCofaceMapComplex.obj`, `unfold` it to `CochainComplex.of`, `erw [CochainComplex.of_d]` (literal `1` vs `0+1`), `objD`/`Fin.sum_univ_two`, `abel`. This is the **first** of the two uncharted differential-unfolds the equalizer needs.
- **Equalizer iso DONE (loop run #4, 2026-06-13, `92a91be`, CI-green run `27454972985`):**
  - `cechHZeroIsoEqualizer : (cechH U 0).obj P ≅ equalizer ((cechCosimpl U P).δ (0:Fin 2)) ((cechCosimpl U P).δ (1:Fin 2))`. Composes `cechHZeroIsoKernel` (H⁰≅ker d⁰) ≪≫ `kernelIsoOfEq cechComplexMod_d_zero_one` (d⁰=δ⁰−δ¹) ≪≫ the preadditive fact *kernel of a difference = equalizer* (`Preadditive.isLimitForkOfKernelFork (kernelIsKernel (δ⁰−δ¹))` `.conePointUniqueUpToIso` `limit.isLimit (parallelPair δ⁰ δ¹)`). This is the **degree-0 Čech/sheaf condition**: global sections = sections agreeing on overlaps. Gotcha: the standalone `δ` occurrences need `(0:Fin 2)`/`(1:Fin 2)` annotations to pin `n=0` (the index is `Fin (n+2)`; without it CI errors "cannot synthesize implicit `n`").
- **Residual (folded into M1b):** the cofaces `δ⁰, δ¹` are still the abstract `cosimplicialObjectFunctor` cofaces — the equalizer is stated *of them*, not yet of coordinate-explicit `Pi.lift (P.map restriction)` maps. The coordinate-unfold (`evalOp`/`mapPower`/`power`/`cech` `@[simps]`, recipe preserved in `docs/ROUTE_RESEARCH_2026_06_13.md` / git history of `NEXT_SESSION.md`) is most natural once `ι = Fin 2` and `𝒪_C` are concrete → it is now an M1b sub-task, not a standalone abstract chip.

⚠️ Env flag (run #1): the local bootstrap `lake build` was running lean
**v4.29.0** while the pin is **v4.30.0-rc2** — verify the toolchain before
trusting local oleans (route doc "Environment flags"). CI (warm, ~3–4 min)
is the working gate meanwhile.

## Rules inherited from the diffgeo challenge post-mortems

- A "named hypothesis" introduced without a same-session discharge on
  arbitrary data is a renamed sorry (paraphrase gate, `CHIP_GATES.md`).
- Single bar: a hole counts CLOSED only when the declaration compiles
  sorry-free/axiom-free against the pinned mathlib AND its statement is
  byte-compatible with `Challenge.lean` (the comparator is the judge —
  do not invent softer tiers).
- Per-item status lives HERE, refreshed every session; prose docs and
  docstrings are not trustworthy for open/closed status.
