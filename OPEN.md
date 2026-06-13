# Open items — jacobian-alggeo-challenge

> **Before any new Lean work: read `CHIP_GATES.md` (repo root)** — vacuity
> lint gate (mechanical, baseline-ratcheted) + the anti-paraphrase gates —
> and `DEVELOPMENT.md` (panic-safe build rules, eval submission mechanics).

## 🛑 GO/NO-GO VERDICT (2026-06-13): NO-GO for the loop — gated on coherent-cohomology infrastructure

The genus (hole 4) forces `FiniteDimensional k H¹(C,𝒪_C)` = Serre finiteness of
coherent cohomology. Confirmed absent from ALL of mathlib at the pin: quasi-coherent
sheaves, coherent sheaves, scheme cohomology, Serre finiteness. The challenge is a
multi-month mathlib-infrastructure program, not a loopable chip sequence. Loop is
DISABLED + `LOOP_HALT` in place. Scope fork (commit infra arc / incremental PRs /
shelve) escalated to Bryan. Full verdict + salvage list:
`docs/ROUTE_RESEARCH_2026_06_13.md` ("M1 GO/NO-GO VERDICT"). All 9 holes remain OPEN.

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
