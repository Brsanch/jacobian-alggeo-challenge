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
| 1 | `genus` | def | **FILLED** (`Submission.genus`, 2026-06-13) — `dim_k H¹(C,𝒪_C)`; sig byte-compatible (`@Submission.genus = @JacobianChallenge.genus` typechecks), sorry/axiom-clean. Value honest pending Segment-3 finiteness; correctness gated by hole 4. |
| 2 | `Jacobian` | def | OPEN |
| 3 | `Jacobian.instGrpObj` | def | OPEN |
| 4 | `Jacobian.smoothOfRelativeDimension_genus` | theorem | OPEN |
| 5 | `Jacobian.instIsProper` | theorem | OPEN |
| 6 | `Jacobian.instGeometricallyIrreducible` | theorem | OPEN |
| 7 | `Jacobian.ofCurve` | def | OPEN |
| 8 | `Jacobian.comp_ofCurve` | theorem | OPEN |
| 9 | `Jacobian.exists_unique_ofCurve_comp` | theorem | OPEN |

### 🅱️ Tower B (Jacobian construction, holes 2,3,5,6,7,8) — SURVEYED 2026-06-13, NO-GO single-session

Declaration-level mathlib survey done at the pin (`docs/ROUTE_RESEARCH_2026_06_13.md`
§"TOWER B survey"). **All six construction holes require a multi-month mathlib-
infrastructure program; none is closable in a session.** Mathlib has zero of the
construction layer: no `Sym^d` of schemes, no scheme quotient by a finite group, **no
coequalizers of `Scheme`** (only `Discrete σ` coproducts), no Picard scheme, no curve
RR, no birational group law. Route-A core (`Sym^d C = C^d/S_d`) hits the ≥5k-LOC STOP
threshold at the *first* gap (P3 = G-invariant affine cover of a quasi-projective
scheme). Route B (FGA Pic⁰) is deeper but native over general `k`. **The A-vs-B
decision is a leap-queue item for Bryan** (`noethersolve/docs/LEAP_QUEUE.md §4`).
- Fork-II bounded piece landed this session: **P1 Noether finiteness of invariants**
  (`Submission/Jacobian/InvariantFiniteness.lean`) — route-independent mathlib-PR
  material, NOT a Route-A commitment, NOT a renamed sorry.

**✅ Tower B BUILT the AFFINE core of M3 (2026-06-13, commits `d61c7c0`, `92205b2`, pushed):**
7 modules under `Submission/Jacobian/` (565 LOC, sorry-free, axiom-clean, vacuity 0, full
`lake build` green, 8327 jobs) — the **affine finite-group quotient `Spec(B^G)`** (generic,
with integral/finite/proper/universally-closed/G-invariant/categorical-quotient-UP) + the
**`S_d`-action on `A^{⊗d}`** (mathlib TODO) + **`Sym^d(Spec A)`** + unconditional finiteness +
Noether invariant finiteness. Holes 2,3,5,6,7,8 STILL OPEN — this is the affine model; the
projective/curve case needs P3 (invariant affine cover of `C^d`) + P5 (`Sym^d C` smooth, `C`
projective), the open walls. Fork-II mathlib-PR material, not a hole-fill. Detail:
`docs/ROUTE_RESEARCH_2026_06_13.md` §"TOWER B build".

**✅ Tower B round 2 extension (2026-06-13, commit `05bf19d`, branch `tower/jacobian-r2`, pushed;
CI run `27476042173`; full `lakelock lake build` green 8336 jobs, vacuity 0, sorry/axiom-free):**
the affine core now carries its **structure over the base** and the **degree-1 identification** —
the pieces the projective construction consumes on every route.
- `Submission/Jacobian/AffineQuotientBase.lean` — `Spec(B^G) ⟶ Spec R` (`structureMorphism`);
  `quotientMap_comp_structureMorphism` (the quotient map descends to `Over (Spec R)`).
- `Submission/Jacobian/AffineSymmetricPowerStructure.lean` — `Sym^d(Spec A)` as an
  `Over (Spec R)` object (`affineSymmetricPowerOver`); **`Sym^1(Spec A) ≅ Spec A`**
  (`affineSymOneIso`, the Abel–Jacobi base case) via `finOneTensorAlgEquiv` (`A^{⊗1} ≃ₐ[R] A`,
  upgrading mathlib's `LinearEquiv`-only `subsingletonEquiv`) + `symOneAlgEquiv`
  (`(A^{⊗1})^{S_1} ≃ₐ[R] A`); **`affineSymOneIso_hom_comp_base`** (the iso is over `Spec R`);
  and **`Sym^0(Spec A) ≅ Spec R`** (`affineSymZeroIso`, the divisor-monoid unit) via
  `finZeroTensorAlgEquiv` (`A^{⊗0} ≃ₐ[R] R`) + `symZeroAlgEquiv`.
- **STILL affine-model foundation, NOT a hole-fill** — holes 2,3,5,6,7,8 OPEN.
- **Globalization leaf-obstruction (verified by mathlib grep at the pin):** **no
  `IsProjective`/`QuasiProjective`/projective-morphism for schemes, no ample line bundles**
  (only `AmpleSet`, the h-principle notion). ⇒ **P5** (`Sym^d C` projective) is *not statable*;
  **P3** (orbit-in-affine-open) has no ample-bundle anchor. The deepest, highest-leverage next
  infra target is the **projective-morphism + ample-line-bundle foundation** itself.
- Next reachable affine-side brick (named, resolved): the **addition / monoid map**
  `Sym^d × Sym^e → Sym^{d+e}` — a multi-step sub-arc (not a one-shot): needs (a) the AlgEquiv
  `A^{⊗(d+e)} ≅ A^{⊗d} ⊗ A^{⊗e}` (`Fin.sumFinEquiv`-reindex; mathlib has `tmulEquiv` only as a
  `LinearEquiv`), equivariant for `S_d × S_e ↪ S_{d+e}`, and (b) `(M ⊗ N)^{G×H} = M^G ⊗ N^H`
  (invariants commute with `⊗`), **free over a field** (`⊗_k` exact) but a genuine mathlib gap
  in general. Build it over `R = k` (the challenge base). This is the algebraic heart of the
  group law (hole 3); the birational group-law extension then needs RR (Tower A).
- Lean note (for the next session): `Spec.map_comp`/`CommRingCat.ofHom_comp` rewriting does NOT
  fire under `rw`/`simp only` when a factor's codomain is `CommRingCat.of ↥(subalgebra)` (the
  `Sym^d` invariant ring); **`erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]` works** (matches up
  to defeq). Used in `affineSymOneIso_hom_comp_base`.

Current phase: **M1 (coherent cohomology canary)** — M0 done (scaffold + CI
green + manifest, `3a3066d`). See `docs/ROUTE_RESEARCH_2026_06_13.md`.

### ✅ Tower-A foundation (round 2): `regular ⇒ domain` in ALL dimensions (2026-06-13, `main` @ `5d3a8ed`, pushed)

`Submission/Cohomology/RegularLocalDomainGeneral.lean` (336 LOC, full `lake build` green
8335 jobs, axioms = `propext`/`Classical.choice`/`Quot.sound` only, vacuity 0, independently
re-verified). Generalizes round-1's `RegularLocalDomain.lean` (dim ≤ 1 only).
- **Thm 1** `spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le` — cotangent /
  embedding-dim drop (`x∈𝔪\𝔪² ⇒ spanFinrank 𝔪(R/(x))+1 ≤ spanFinrank 𝔪(R)`), reusable.
- **Thm 2** `isDomain_of_isRegularLocalRing` (Stacks 00NP) — regular local ring, any dim ⇒ domain.

**Foundation, NOT a hole-fill.** Closes the `regular ⇒ domain` leaf of Wall 2; the remaining
Wall-2 gap **`smooth ⇒ regular local`** still bottoms out (compile-verified absent at the pin) in
(1) the finite-type-over-field **dimension formula** (`dim` of a standard-smooth local `k`-algebra
= rel dim; `KrullDimension/Field.lean` has only `dim field = 0`, no `dim=trdeg`), and (2) the
**residue-field cotangent sequence** `finrank_κ(𝔪/𝔪²)=rel dim` (`StandardSmoothCotangent` gives
`rank_S Ω`, a different `CotangentSpace`). Wall 1 (Serre finiteness) unchanged; all 9 holes OPEN.
Detail: `docs/ROUTE_RESEARCH_2026_06_13.md` §"TOWER A — round-2 brick".

### ✅ Stack-I bricks I.1 + I.2 BUILT (2026-06-14/15) — Pic of sheaves of modules exists

> **UPDATE (2026-06-15):** I.1a is **DONE** (`sheafificationW_isMonoidal`, the internal-hom arc
> pieces I–III + whiskering, `PresheafOfModulesSheafHom.lean` + `SheafificationWMonoidal.lean`), so
> I.1 (`SheafOfModules` monoidal) is unconditional given `α`; and **I.2 is DONE** (`Picard.lean`:
> `Pic D` for any monoidal category, `SheafOfModules.Pic α` a `CommGroup`). Stack I = I.0/I.1/I.2 ✓
> of ~6; sorry/axiom-free, vacuity 0, single-universe. **All 9 holes still OPEN** — this is
> foundation, and `Pic` here is the *abstract* group, not the *scheme* `Pic⁰` (Wall δ). The A-vs-B
> route fork is now reachable. Driving docs: `NEXT_SESSION.md`,
> `docs/{SHARED_FOUNDATION_ROUTE_2026_06_13,PIECE_III_SHEAF_PRESERVATION_ROUTE_2026_06_14}.md`. The
> historical scaffold note below is superseded.

### 🟡 (superseded) Shared-foundation brick I.1 (2026-06-13): `MonoidalCategory (SheafOfModules R)` — scaffold + reduction to ONE classical theorem

A-vs-B route leap **deferred** (Bryan, 2026-06-13): build the foundation BOTH routes need
first (`docs/SHARED_FOUNDATION_ROUTE_2026_06_13.md`). The bottom brick is the tensor structure
on sheaves of modules (Route B represents `Pic⁰`; Route A needs line bundles for ample —
nothing in Stack I builds without it). `Submission/Cohomology/SheafOfModulesMonoidal.lean`
(163 LOC, full build green 8340 jobs, axioms = `propext`/`Classical.choice`/`Quot.sound`,
vacuity 0, independently re-verified):
- Builds `SheafOfModules.monoidalCategory α : MonoidalCategory (SheafOfModules R)` by transporting
  `PresheafOfModules.monoidalCategory` through the sheafification localization
  (`CategoryTheory.Localization.Monoidal`; defeq type-synonym transport, no equivalence machinery).
- **Honest status — this is scaffold + a precise REDUCTION, NOT a usable monoidal structure yet.**
  The instance is **conditional on `[(sheafificationW J R₀).IsMonoidal]`** (mathlib's own class,
  in exact analogy with mathlib's `CategoryTheory.Sheaf.monoidalCategory`; NOT an invented
  named-hypothesis, NOT vacuous — vacuity gate confirms). The undischarged hypothesis is the
  genuine remaining content: **`W.IsMonoidal` = "sheafification commutes with the tensor product"**
  (Stacks 17.16 / EGA 0_I.4.1), traced to its leaf — absent at the pin (no
  `MonoidalClosed (PresheafOfModules)`, no sheafification-preserves-tensor lemma; `IsLeftAdjoint`
  alone is insufficient). **It is a genuine, separate, strictly-foundational classical theorem —
  NOT circular with the conclusion.**
- **I.1a obstruction TRACED TO LEAVES (2026-06-13, warm cache; route doc §"SHARED-FOUNDATION brick
  I.1a", `LEAP_QUEUE §6`).** `J.W = ObjectProperty.isLocal (IsSheaf J)` (orthogonality to sheaves);
  the clean discharge mirrors mathlib's `Sites/Monoidal.lean` and needs a **concrete internal hom
  of presheaves of modules over a *varying* ring** + `IsSheaf H ⟹ IsSheaf [F,H]` + a ~30-line port.
  Mathlib omits this (only the fixed-ring `ModuleCat/Monoidal/Closed.lean`; `Enriched.FunctorCategory`
  is constant-enrichment only). **Two shortcuts ruled out:** (1) SAFT gives `MonoidalClosed
  (PresheafOfModules)` abstractly (`tensorLeft F` preserves colimits + `freeYoneda` separator +
  `WellPowered`) but the formula-free adjoint can't prove sheaf-preservation → **off critical path**
  (still a clean fork-II PR); (2) the direct local-bijectivity route dies on tensor non-left-exactness.
  ⇒ I.1a is a multi-hundred-LOC, multi-session build reaching only I.2 (`Pic`), **below the deferred
  A-vs-B leap (§4)**. Build-vs-pivot is a human-leap decision (surfaced to Bryan 2026-06-13).
- **I.1a BUILD STARTED — Bryan chose "Build I.1a now" (2026-06-13).**
  `Submission/Cohomology/PresheafOfModulesInternalHom.lean`. Decomposition + every mathlib handle:
  route doc §"I.1a BUILD". **✅ Piece (I) DONE** — `sheafificationW_eq_isLocal`
  (`sheafificationW = ObjectProperty.isLocal (· ∈ range (localInclusion α).obj)`, the Bousfield
  local-class form) + consumable `sheafificationW.bijective_precomp`. Via
  `inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` + `isLocal_eq_inverseImage_isomorphisms`
  on `sheafificationAdjunction α` (right adjoint `SheafOfModules.forget ⋙ restrictScalars α` is
  fully faithful). **NEXT = piece (II)** (concrete internal hom `[F,H]` + tensor-hom adjunction,
  the bulk), then piece (III) sheaf-preservation (mirror `Presheaf.IsSheaf.hom`), then the port.

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

### ✅ Segment 2 DONE + hole 1 filled (2026-06-13, `Submission/StructureSheafCohomology.lean`, full-build green)

`H¹(C, 𝒪_C)` as a `k`-module + the genus. Sorry/axiom-clean, vacuity-lint 0,
throttled full `lake build` green (8320 jobs).
- `kStruct C : const k ⟶ 𝒪_C` — the `k`-algebra structure on the structure sheaf,
  from the structure morphism `C.hom : C.left ⟶ Spec k` (`k ≅ Γ(Spec k) →⟮appTop⟯
  Γ(C.left,⊤) →⟮restrict⟯ 𝒪_C(U)`).
- `structurePresheafUnder C : (Opens C.left)ᵒᵖ ⥤ Under (CommRingCat.of k)` — `𝒪_C`
  as a presheaf of `k`-algebras; `… ⋙ underToModuleCat` ⇒ `structurePresheafModule C`
  valued in `ModuleCat k`.
- `structureSheafModule C : Sheaf (Opens.grothendieckTopology C.left) (ModuleCat k)`
  — the sheaf condition **transports for free**: the `ModuleCat k` version's
  underlying `Type`-presheaf is *defeq* to the `CommRingCat` structure sheaf's, and
  `forget (ModuleCat k)` reflects limits (`isSheaf_of_isSheaf_comp`). The whole
  construction reuses `C.left.IsSheaf` — no new sheaf-gluing.
- `H1 C := H _ k 1 (structureSheafModule C)` — `H¹(C,𝒪_C)`, a `k`-module (Segment 1).
- `genusH1 C := Module.finrank k (H1 C)`; **`Submission.genus`** fills hole 1 with it.

**Gate-6 wins (no hypotheses to discharge):** `HasSheafify (Opens.grothendieckTopology
C.left) (ModuleCat k)` resolves *automatically* at the pin (general instance for a
target whose `forget` preserves limits + small covers) — so the curve's opens site
feeds `H` directly. Combined with Segment 1's auto-`HasExt`/`Linear k`/`Module k (Ext)`,
the entire fork-B cohomology of the curve needed **zero** carried typeclass hypotheses.

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
