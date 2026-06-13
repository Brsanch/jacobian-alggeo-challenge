# Tower C — rigidity of abelian varieties + obstruction map (2026-06-13)

Branch `tower/abelian-variety`. All Lean below is sorry-free, axiom-free
(`#print axioms` = `{propext, Classical.choice, Quot.sound}`), vacuity-lint 0,
local `lake build` green, CI green. Files under `Submission/AbelianVariety/`.

## Delivered (genuine classical content, ~480 LOC)

### `PointedDiff.lean` — categorical reduction
The companion to mathlib's `isCommMonObj_iff_commutator_eq_toUnit_η`. For a map
`h : A ⟶ B` of group objects in any cartesian-monoidal category, the
**pointed-difference map**
`pointedDiff h := (μ[A] ≫ h) · ((fst ≫ h) · (snd ≫ h))⁻¹ : A ⊗ A ⟶ B`
(in the group `Hom(A⊗A, B)`) measures the failure of `h` to be a homomorphism:
- `isMonHom_iff_pointedDiff_eq` — a pointed `h` is `IsMonHom` iff `pointedDiff h`
  is the constant unit;
- `lift_one_comp_pointedDiff`, `lift_unit_pointedDiff`, `whiskerLeft_η_pointedDiff`
  — `pointedDiff h` vanishes on the `A × {e}` / `{e} × A` axes (ω-binder-free
  analogues of mathlib's `whiskerLeft_η_commutator`).

### `Rigidity.lean` — Mumford's rigidity lemma (AV §4)
- `pointedDiff_eq_toUnit_η_of_isAlgClosed` — over an **algebraically closed**
  field: `pointedDiff h` is constant. The geometric core; adapts
  `isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`'s
  Zariski's-Main-Theorem + completeness + `JacobsonSpace` constancy argument to
  `gam = lift (fst A A) (pointedDiff h) : A⊗A → A⊗B`.
- `pointedDiff_eq_toUnit_η_of_geometricallyIntegral` — over an **arbitrary** field,
  by base change to `k̄` + `(Over.pullback fK).map_injective` (descent à la
  `..._of_geometricallyIntegral`). The descent `simpa` set, beyond commutator's:
  `Functor.map_comp`, `Functor.obj.μ_def` (the extra `μ[A]≫h` term),
  `Functor.Monoidal.μIso_hom`, and the `_assoc` projection lemmas
  `μ_fst_assoc`/`μ_snd_assoc` (the projections carry a trailing `≫ F.map h`).
- **`isMonHom_of_pointed_of_geometricallyIntegral`** — *a pointed morphism of
  abelian varieties over any field `k` is a group-object homomorphism.* This IS
  the rigidity input **hole 9's uniqueness** (`exists_unique_ofCurve_comp`)
  consumes.

### `Homomorphisms.lean` — consequences for morphisms (AV §4 corollaries)
- `isMonHom_iff_pointed` — *a morphism of abelian varieties is a homomorphism iff
  it preserves the identity.*
- `pointedPart f := f · (e ↦ f e)⁻¹`; `eq_pointedPart_mul_const` — **every
  morphism is a homomorphism followed by a translation**; `const_eq_of_decomp` +
  `pointedPart_eq_of_decomp` — this decomposition is **unique**.
- `pointedPart_mul`, `pointedPart_pointedPart`, `pointedPart_one'`,
  `isMonHom_iff_pointedPart_eq_self`, `isMonHom_constMap_iff` — `pointedPart` is
  the canonical **retraction group-homomorphism** `Hom(A,B) → Hom(A,B)` onto the
  subgroup of homomorphisms.

## Obstruction map (why the rest is walled — state, don't grind)

The arc is FGA-grade; all three parallel towers independently hit deep walls.
Tower C's remaining pieces are blocked as follows.

1. **Smoothness over a general field `k`** (brief core item #1; hole 4's smoothness
   half). mathlib has `smooth_of_grpObj_of_isAlgClosed` (group scheme over `k̄`,
   reduced, lfp ⇒ smooth). The general-`k` upgrade funnels — for *every* route
   (base-change descent; direct translation à la the alg-closed proof; geometric
   reducedness ⇒ smooth) — through **faithfully-flat descent of (formal)
   smoothness**: `RingHom.FormallySmooth` (or `RingHom.Smooth`) **codescends along
   faithfully-flat ring maps**. Verified absent at the pin: `RingHom.Smooth`/
   `FormallySmooth` have `isStableUnderBaseChange`, `localizationPreserves`,
   `propertyIsLocal`, `holdsForLocalizationAway`, `OfLocalizationSpanTarget` — but
   **no codescent**; `AlgebraicGeometry/Morphisms/Descent.lean`'s own TODO confirms
   even affine-morphism faithfully-flat descent is unbuilt. This is a genuine,
   deep, classical theorem (fpqc-locality of smoothness on the base, via the
   cotangent complex / lifting-criterion descent) — a multi-week mathlib PR, not a
   session bridge. **Single missing lemma to unblock: `RingHom.FormallySmooth`
   codescends along faithfully-flat.**

2. **Hole 9 wiring.** `isMonHom_of_pointed_of_geometricallyIntegral` is the rigidity
   *input*; instantiating it at `A := Jacobian C` and packaging the `∃!` needs
   Tower B's `Jacobian C` + `ofCurve`. The uniqueness mechanism's substrate exists
   (`IsSchemeTheoreticallyDominant` + `Scheme.Hom.app_injective`), but the
   "`ofCurve(C)` generates `Jacobian C`" property is Tower B's. Integration, not
   theory.

3. **General rigidity lemma** (`f : X ⊗ Y ⟶ Z` factoring through `pr_Y`). The
   textbook statement would re-transcribe the same ~70-line ZMT argument already in
   `Rigidity.lean` for a general `f` (gate-2 duplication) and reintroduces the
   no-rational-point subtlety over non-closed `k` (abelian varieties dodge it via
   `η`). Not built: low marginal value over the delivered specific result.

## Decisive-regime verdict
The independent core (rigidity + its corollaries) is **complete and clean at
~480 LOC** — well inside the ~5k ceiling. Per the repo gate, the bounded clean
pieces are landed (and are upstreamable mathlib-PR material: rigidity of abelian
varieties is absent from mathlib); the walls above are stated at maximum
resolution rather than ground through with stubs.
