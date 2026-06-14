# Route research — Front B / Wall 1: Serre finiteness `FiniteDimensional k (H1 C)` (2026-06-14)

The Stack-II `DONE WHEN`. This is the genus certifier (hole 1's honest value) and the input to
Riemann–Roch. The brief: "scope it as its own route doc section when you start it." This is that doc,
grounded in a warm-cache mathlib survey (pin `5450b53e5ddc`).

## Target (exact)

`FiniteDimensional k (H1 C)` where (`StructureSheafCohomology.lean`)

```
H1 C := H (Opens.grothendieckTopology C.left) k 1 (structureSheafModule C)
      = Ext (coeffSheaf …) (structureSheafModule C) 1   -- in  Sheaf (Opens.gt C.left) (ModuleCat k)
```

i.e. **degree-1 derived-functor sheaf cohomology of `𝒪_C`, taken in the `k`-linear Grothendieck-abelian
category `Sheaf (opens-site of C.left) (ModuleCat k)`**, as the `Ext¹` out of the constant sheaf `k`.
The `k`-module structure is `Abelian.Ext.instModule` (k-linear abelian ⇒ Ext is a k-module); this is
exactly why `H1 C` is type-correct for `FiniteDimensional k`. `genus C = finrank k (H1 C)` is already a
filled bare `def` (junk `0` if infinite); this arc makes the value honest.

## mathlib substrate survey (warm cache, 2026-06-14)

**PRESENT (usable spine):**
- **Mayer–Vietoris square from an opens cover, FREE** — `Opens.mayerVietorisSquare (U V : Opens T) :
  (Opens.grothendieckTopology T).MayerVietorisSquare` (`Topology/Sheaves/MayerVietoris.lean:59`), with
  `X₁ = U⊓V, X₂ = U, X₃ = V, X₄ = U⊔V`. **No hypothesis** — every pair of opens is an MV square for the
  opens site. For a 2-cover `U ⊔ V = ⊤`, `X₄ = ⊤` and `H^n(X₄) = H^n(C)`.
- **MV long exact sequence in sheaf cohomology** — `GrothendieckTopology.MayerVietorisSquare.sequence` /
  `sequence_exact` (`Sites/SheafCohomology/MayerVietoris.lean`): the 6-term exact
  `H^{n₀}(X₄) → H^{n₀}(X₂)⊞H^{n₀}(X₃) → H^{n₀}(X₁) →[δ] H^{n₁}(X₄) → H^{n₁}(X₂)⊞H^{n₁}(X₃) → H^{n₁}(X₁)`.
  **Stated for `AddCommGrpCat`-valued sheaves only** (the file fixes `A = AddCommGrpCat`).
- **`ModuleCat.finite_ext`** (`Algebra/Category/ModuleCat/Ext/Finite.lean:28`): `Ext N M i` is
  `Module.Finite R` when `N M` are, over a Noetherian `R` — **but this is Ext in `ModuleCat R`, not in
  `Sheaf J (ModuleCat k)`.** Not directly applicable; it is the *target shape* the cokernel finiteness
  (W3) must reach.
- **Flasque sheaves** — `TopCat.Sheaf.IsFlasque` + short-exact-sequence behaviour
  (`Topology/Sheaves/Flasque.lean`). The classical acyclic-resolution carrier, but the connection
  `flasque ⇒ H^{>0} = 0` is **NOT** present.
- `Sheaf.H` / `cohomologyPresheaf` / `H'` derived API (`Sites/SheafCohomology/Basic.lean`);
  `Sheaf.Γ` global sections + `H⁰ ≅ Γ` (this repo's `HZeroAddEquivΓ`).
- Čech cochain functor `cechComplexFunctor` (`Sites/SheafCohomology/Cech.lean`) — but **no
  Čech↔derived comparison theorem** (no acyclic-cover ⇒ Čech = derived).

**ABSENT (the real content to build):**
- No quasi-coherent / coherent sheaves in `AlgebraicGeometry/` (grep clean).
- No **affine acyclicity** `H^{>0}(affine, 𝒪) = 0` (Serre's vanishing); no Serre affineness criterion.
- No **Grothendieck vanishing** `H^{>dim} = 0`; no cohomological-dimension theory.
- No **finiteness of sheaf cohomology** for proper schemes; no proper-pushforward-of-coherent.
- No `ModuleCat k`-valued MV sequence (only `AddCommGrpCat`).
- No 2-affine **cover** of the curve as a usable object (the curve `C` carries no cover datum; Serre's
  "curve minus a finite set is affine" is absent).

## The route: Mayer–Vietoris on a 2-affine cover (Hartshorne III.4 lineage)

Pick affine opens `U, V` with `U ⊔ V = ⊤` (covering the curve) and `U ⊓ V` affine. The MV LES at `n₀=0,
n₁=1` reads, since `H^1(C) = H^1(⊤) = H^1(X₄)`:

```
H⁰(U)⊞H⁰(V) →[ρ] H⁰(U⊓V) →[δ] H¹(C) →[r] H¹(U)⊞H¹(V) → H¹(U⊓V)
```

- If `U, V` are affine and **acyclic** (`H¹(U)=H¹(V)=0`, W2), then `r = 0` and **`H¹(C) ≅ coker ρ =
  H⁰(U⊓V) / (im H⁰(U) + im H⁰(V))`** — the "principal parts modulo regular parts," the classical genus
  presentation.
- `H⁰(W) = Γ(W, 𝒪)` is the (infinite-dimensional over `k`) coordinate ring of the affine `W`; the
  cokernel is nonetheless **finite-dimensional** (W3) — this is the Riemann–Roch content.

`FiniteDimensional k (H1 C)` then follows from **(W2) affine acyclicity** + **(W3) cokernel finiteness**,
once the diagram is set up in the **k-linear** category (W1) over a **cover** that exists (W0).

## Located walls (reachability, hardest last)

- **(W1) `ModuleCat k`-valued MV long exact sequence — ✅ BUILT 2026-06-14**
  (`Submission/Cohomology/MayerVietorisModuleCat.lean`, full build 8351 jobs / vacuity 0 / axioms
  clean). The port went through exactly as planned: the two `ModuleCat.free k` instances missing at the
  pin (`IsLeftAdjoint` from `ModuleCat.adj`; `PreservesMonomorphisms` by the verbatim `AddCommGrpCat`
  split-mono/empty-case proof) are supplied, then `isPushoutModuleCatFreeSheaf` / `shortComplex` /
  `shortComplex_shortExact` mirror mathlib, and `mayerVietoris_ext_exact` applies the generic
  `Abelian.Ext.contravariantSequence_exact` to get the 6-term exact MV LES
  `Ext(k[X₄],F,n₀) → Ext(k[X₂]⊞k[X₃],F,n₀) → Ext(k[X₁],F,n₀) →δ Ext(k[X₄],F,n₁) → ⋯` in
  `Sheaf J (ModuleCat k)`. The remaining connector to `H1 C` is the **`coeffSheaf ≅ k[⊤]`
  identification** (constant sheaf `k` = sheafified free `k`-module on the terminal representable), so
  `Ext(k[X₄=⊤], F, 1) = H1 C` — a follow-on lemma. Original plan notes preserved below:

  mathlib's MV LES is `AddCommGrpCat`-only; `H1 C`
  is `Ext` in `Sheaf J (ModuleCat k)` (k-linear, the structure we need for `FiniteDimensional k`). Ext
  does **not** commute with the forgetful `Sheaf(ModuleCat k) → Sheaf(AddCommGrp)`, so the AddCommGrp
  sequence cannot be borrowed; the MV LES must be re-derived for `A = ModuleCat k`. **Concrete plan
  (verified against the mathlib source):** the MV LES is `Ext.contravariantSequence` (a GENERIC
  contravariant-`Ext` LES, valid in any abelian category with `HasExt`) applied to
  `MayerVietorisSquare.shortComplex_shortExact` — a short exact sequence of **free-`AddCommGrpCat`
  sheaves** `0 → ℤ[X₁] → ℤ[X₂]⊕ℤ[X₃] → ℤ[X₄] → 0` built from `yoneda.obj Xᵢ ⋙ AddCommGrpCat.free` and
  `presheafToSheaf` (the `isPushoutAddCommGrpFreeSheaf` argument: left adjoints `free`+sheafification
  preserve the MV-square pushout). So the port is: (i) build the analogous **free-`k`-module sheaf**
  short complex `0 → k[X₁] → k[X₂]⊕k[X₃] → k[X₄] → 0` (`yoneda.obj Xᵢ ⋙ ModuleCat.free k ⋙
  presheafToSheaf`) + its `ShortExact` (same left-adjoint pushout argument, with `ModuleCat.free k`);
  (ii) apply the generic `Ext.contravariantSequence_exact` to get the LES involving `Ext(k[Xᵢ], F, n)`;
  (iii) **identify `coeffSheaf` (constant sheaf `k`) with the `X₄=⊤` term** `k[⊤]` (sheafified free
  `k`-module on the terminal representable), so the `Ext(k[⊤], F, 1)` term **is** `H1 C`. Substantial
  (~the MV file's content, several hundred LOC of category theory) but bounded and mechanical-ish.
  **Recommended first brick — the spine that turns W2/W3 into isolated named targets; buildable now
  without the W2 route decision.**
- **(W0) the 2-affine cover.** Need affine opens `U, V` with `U⊔V = ⊤`, `U⊓V` affine. Classical for a
  projective curve (complements of hyperplane sections), but the *existence* (and `U⊓V` affine =
  separatedness) is itself absent and ⇐ Serre's affineness / "curve minus finite set is affine." A real
  sub-arc; for the challenge curve it must be produced from `IsProper` + `SmoothOfRelativeDimension 1`.
- **(W2) affine acyclicity `H¹(affine, 𝒪) = 0`.** The deepest wall. The opens-site derived `H¹` of the
  structure sheaf on an affine. The classical proof is QC-cohomology-vanishing on affines (Serre,
  Stacks 01XB) — and **mathlib has no quasi-coherent sheaf cohomology at all**. Two sub-routes, both
  multi-session: (i) build QC cohomology + Serre vanishing; (ii) a flasque/Godement resolution of `𝒪`
  on the affine and `flasque ⇒ acyclic` (needs building `flasque ⇒ H^{>0}=0`, also absent). This is the
  bottleneck that determines whether Front B is reachable this quarter.
- **(W3) cokernel finiteness `finrank_k (H⁰(U⊓V)/(H⁰U + H⁰V)) < ∞`.** Riemann–Roch content. Needs the
  algebraic structure of the curve (the cover sections are f.g. `k`-algebras; the quotient is finite by
  a Noether-normalization / partial-fractions argument over the affine line). Real, but more
  self-contained than W2 once W0 gives the cover.

## Decisive-regime verdict

Front B is **reachable in architecture** (MV spine + cover-to-square are present and free) but **gated
on two mathlib-absent theorems** — affine acyclicity (W2) and cokernel finiteness (W3) — each a
multi-session build, with W2 the true bottleneck (it needs QC-sheaf cohomology or a flasque-acyclicity
arc that mathlib lacks entirely). There is **no quick brick** that delivers `FiniteDimensional k (H1 C)`.

**Recommended brick order:**
1. **(W1) `ModuleCat k` MV long exact sequence** for `H1 C` — reachable spine; isolates W2/W3. *(first)*
2. **(W0) 2-affine cover** of the proper smooth curve (or carry it as a genuine geometric hypothesis at
   first, discharged later) → instantiate `Opens.mayerVietorisSquare U V` with `U⊔V = ⊤`.
3. **(W2) affine acyclicity** `H¹(affine, 𝒪) = 0` — the bottleneck; likely its own QC-cohomology or
   flasque-resolution sub-arc. *Attack the falsification-first question here: is flasque⇒acyclic
   reachable on the opens site, or is full QC cohomology unavoidable?*
4. **(W3) cokernel finiteness** → `FiniteDimensional k (H1 C)`; then Riemann–Roch.

This is a `feedback_obstruction_then_human_leap` handoff point: W2 (does Front B need QC-sheaf
cohomology built from scratch, or is the flasque route shorter?) is the route decision for Bryan. W1 is
buildable now without that decision.

## Alternatives considered (deferred)

- **Finite map to `ℙ¹` + pushforward.** Noether-normalize the curve to a finite map `C → ℙ¹`, push `𝒪_C`
  forward, use `H¹(ℙ¹, ·)`. Needs proper/finite pushforward of cohomology AND `H¹(ℙ¹, 𝒪)` — both absent;
  strictly more machinery than MV.
- **Projective embedding + Serre twist (`O(n)`, Serre vanishing).** The Hartshorne III.5 finiteness
  route; needs projective space cohomology and the twisting sheaves — far more absent infrastructure.
- **Čech = derived directly.** `cechComplexFunctor` exists but the comparison theorem (acyclic cover ⇒
  Čech computes derived) is absent; reduces to the same affine-acyclicity wall (W2) plus a comparison
  build. MV (which mathlib *does* provide as a derived LES) short-circuits the comparison for the
  2-cover case — hence the chosen route.

## Sources

- Hartshorne, *Algebraic Geometry* III.2 (Grothendieck vanishing III.2.7), III.3 (Serre affineness
  criterion III.3.7), III.4 (Čech, affine acyclicity III.4.5), III.5 (finiteness via ℙⁿ).
- Stacks: 01XB / 01EW (QC cohomology vanishes on affines), 01EO / 03F7 (Čech-to-derived), 02UZ
  (Grothendieck vanishing), 02O3 (proper pushforward of coherent is coherent).
- mathlib: `Topology/Sheaves/MayerVietoris.lean`, `Sites/SheafCohomology/{Basic,MayerVietoris,Cech}.lean`,
  `Algebra/Category/ModuleCat/Ext/Finite.lean`, `Topology/Sheaves/Flasque.lean`.

Foundation scoping; certifies no hole yet. Updates `LEAP_QUEUE §5` (Wall 1).
