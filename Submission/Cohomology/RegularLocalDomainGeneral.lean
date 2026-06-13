import Mathlib

/-!
# `IsRegularLocalRing ⇒ IsDomain` in **arbitrary dimension** (Stacks 00NP)

The companion file `RegularLocalDomain.lean` proves the `dim ≤ 1` case of "a regular local ring
is a domain" by an explicit `tᵏ·unit` factorisation of the principal maximal ideal. That argument
does not generalise: for `dim ≥ 2` the maximal ideal is not principal. This file proves the
**general-dimension** statement by induction on the embedding dimension, the classical Serre /
Atiyah–Macdonald argument (Stacks 00NP):

* **Theorem 1** (`spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le`): modding a
  Noetherian local ring by an element `x ∈ 𝔪 \ 𝔪²` drops the minimal number of generators of the
  maximal ideal (the embedding dimension) by at least one. This is the cotangent-space
  rank-drop, proved through mathlib's `CotangentSpace.span_image_eq_top_iff` generating-set
  criterion — no residue-field rank–nullity needed.

* **Theorem 2** (`isDomain_of_isRegularLocalRing`): a regular local ring of any dimension is a
  domain. Strong induction on `dim`: choose a parameter `x ∈ 𝔪 \ 𝔪²` avoiding all minimal primes
  (prime avoidance); `R/(x)` is regular of dimension one less (Theorem 1 + the parameter
  dimension-drop `supportDim_quotSMulTop_succ_eq_…`), hence a domain by induction, so `(x)` is
  prime; a minimal prime `q ≤ (x)` satisfies `q ⊆ 𝔪·q`, so `q = ⊥` by Nakayama, whence `⊥` is
  prime and `R` is a domain.

mathlib at the pin has `RegularLocalRing/Defs.lean` only (the definition + the cotangent
criterion); it has **no** `regular ⇒ domain` in any dimension. Self-contained, upstreamable.

No `sorry`, no `axiom`, no `ω` binders.
-/

open IsLocalRing
open scoped Pointwise

namespace JacobianAlggeo

/-! ## Local instance: a proper-ideal quotient of a local ring is local.

`maximalIdeal (R ⧸ Ideal.span {x})` only typechecks once `IsLocalRing (R ⧸ Ideal.span {x})` is in
scope. For `x ∈ 𝔪` the ideal `(x)` is proper, hence `R ⧸ (x)` is nontrivial and local; we expose a
`Nontrivial`-keyed local instance so the statement of Theorem 1 elaborates (the caller discharges
`Nontrivial` from `x ∈ 𝔪`). -/
local instance isLocalRing_quotient_of_nontrivial
    {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    [Nontrivial (R ⧸ Ideal.span {x})] : IsLocalRing (R ⧸ Ideal.span {x}) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective

/-! ## Theorem 1 — the cotangent / embedding-dimension drop -/

/-- **Cotangent rank-drop.** If `x` lies in `𝔪 \ 𝔪²` of a Noetherian local ring `R`, then the
embedding dimension of `R ⧸ (x)` is at least one less than that of `R`:
`spanFinrank 𝔪(R/(x)) + 1 ≤ spanFinrank 𝔪(R)`.

(The `[Nontrivial (R ⧸ Ideal.span {x})]` binder is automatically satisfied: `x ∈ 𝔪` forces `(x)`
proper. It is present only so the conclusion's `maximalIdeal (R ⧸ (x))` elaborates; the caller
supplies it via `haveI` from `hx`.) -/
theorem spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} [Nontrivial (R ⧸ Ideal.span {x})]
    (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ (IsLocalRing.maximalIdeal R) ^ 2) :
    (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1
      ≤ (IsLocalRing.maximalIdeal R).spanFinrank := by
  classical
  set m := maximalIdeal R with hm
  set κ := ResidueField R
  set V := CotangentSpace R with hV
  -- the cotangent class of `x` is nonzero since `x ∉ 𝔪²`.
  set xbar : V := Ideal.toCotangent m (⟨x, hx⟩ : m) with hxbar
  have hxbar_ne : xbar ≠ 0 := by
    rw [hxbar, Ne, m.toCotangent_eq_zero (⟨x, hx⟩ : m)]; exact hx2
  -- embedding dimension = finrank of the cotangent space.
  have hd : (m).spanFinrank = Module.finrank κ V :=
    spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R
  -- a complement `W` of the line through `xbar`; a basis of `W` plus `xbar` spans `V`.
  obtain ⟨W, hWc⟩ := Submodule.exists_isCompl (Submodule.span κ {xbar})
  -- `finrank W = d - 1`.
  have hsum : Module.finrank κ (Submodule.span κ {xbar}) + Module.finrank κ W
      = Module.finrank κ V := Submodule.finrank_add_eq_of_isCompl hWc
  rw [finrank_span_singleton hxbar_ne] at hsum
  -- a finite basis of `W`, lifted to vectors of `V`.
  set n := Module.finrank κ W with hn
  set b : Module.Basis (Fin n) κ W := Module.finBasis κ W with hb
  -- the spanning set in `V`: lifts of the basis vectors.
  set t : Set V := Set.range (fun i : Fin n => (b i : V)) with ht
  -- `span κ t = W`: the lifts of a basis of `W` span `W` inside `V`.
  have hWeq : Submodule.span κ t = W := by
    have hbtop : Submodule.span κ (Set.range (b : Fin n → ↥W)) = ⊤ := b.span_eq
    have : (Submodule.span κ (Set.range (b : Fin n → ↥W))).map W.subtype = W := by
      rw [hbtop, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span] at this
    rw [ht]
    rw [show (fun i : Fin n => (b i : V)) = (W.subtype ∘ b) from rfl, Set.range_comp] at *
    exact this
  -- `{xbar} ∪ t` spans `V = ⊤`.
  have hspanV : Submodule.span κ (insert xbar t) = ⊤ := by
    rw [Submodule.span_insert, hWeq, hWc.sup_eq_top]
  -- transport to the generating-set criterion: need a set of elements of `↥m`.
  -- lift `xbar` and each `b i` to elements of `↥m`.
  -- use `⟨x, hx⟩` itself as the chosen preimage of `xbar` (so its value in `R` is exactly `x`).
  set xm : m := ⟨x, hx⟩ with hxmdef
  have hxm : Ideal.toCotangent m xm = xbar := rfl
  have hlift : ∀ i : Fin n, ∃ y : m, Ideal.toCotangent m y = (b i : V) := fun i =>
    Ideal.toCotangent_surjective m (b i : V)
  choose g hg using hlift
  -- the set `s ⊆ ↥m` whose cotangent image is `{xbar} ∪ t`.
  set s : Set m := insert xm (Set.range g) with hs
  -- the cotangent image of `s` is exactly `insert xbar t`.
  have himage : Ideal.toCotangent m '' s = insert xbar t := by
    rw [hs, Set.image_insert_eq, hxm]
    congr 1
    rw [← Set.range_comp, ht]
    ext v
    simp only [Set.mem_range, Function.comp_apply]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, by rw [← hg i]; exact hi⟩,
      fun ⟨i, hi⟩ => ⟨i, by rw [hg i]; exact hi⟩⟩
  -- so `span R s = ⊤` in `Submodule R ↥m`.
  have hspanR : Submodule.span R s = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, himage, hspanV]
  -- push to the ideal level: `m = span R (m.subtype '' s)`.
  have hmspan : m = Ideal.span (Submodule.subtype m '' s) := by
    have h1 : (Submodule.span R s).map (Submodule.subtype m) = m := by
      rw [hspanR, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span] at h1
    exact h1.symm
  -- the maximal ideal of the quotient is the image of `m`.
  have hmapmax : (m).map (Ideal.Quotient.mk (Ideal.span {x}))
      = maximalIdeal (R ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  -- the image set: `mk '' (m.subtype '' s)`; `mk x = 0`.
  -- generating set for the quotient maximal ideal.
  set q := Ideal.Quotient.mk (Ideal.span {x}) with hq
  -- the generating multiset of the quotient maximal ideal, `q '' (range g pushed to R)`.
  set G : Set (R ⧸ Ideal.span {x}) := q '' ((Subtype.val : m → R) '' (Set.range g)) with hG
  have hcoe : (Submodule.subtype m : m → R) = (Subtype.val : m → R) := m.coe_subtype
  have hqx : q x = 0 := by
    rw [hq, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span (Set.mem_singleton x)
  have hgenset : maximalIdeal (R ⧸ Ideal.span {x}) = Ideal.span G := by
    rw [← hmapmax, hmspan, Ideal.map_span, hcoe, hG]
    -- `Subtype.val '' s = insert x (Subtype.val '' range g)`; `q x = 0`, so the span drops it.
    have hsplit : (Subtype.val : m → R) '' s
        = insert x ((Subtype.val : m → R) '' (Set.range g)) := by
      rw [hs, Set.image_insert_eq]
    rw [hsplit, Set.image_insert_eq, hqx, Ideal.span_insert_zero]
  -- bound the embedding dimension of the quotient by `card (range g) ≤ n = d - 1`.
  have hGfin : G.Finite := ((Set.finite_range g).image _).image _
  have hle1 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ G.ncard := by
    rw [hgenset]
    exact Submodule.spanFinrank_span_le_ncard_of_finite hGfin
  have hcard_le : G.ncard ≤ n := by
    have h1 : G.ncard ≤ (Set.range g).ncard := by
      rw [hG]
      exact (Set.ncard_image_le ((Set.finite_range g).image _)).trans
        (Set.ncard_image_le (Set.finite_range g))
    have h2 : (Set.range g).ncard ≤ n := by
      have := Set.ncard_image_le (s := (Set.univ : Set (Fin n))) (f := g) Set.finite_univ
      rw [Set.image_univ, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
      exact this
    exact h1.trans h2
  -- assemble: `spanFinrank quotient + 1 ≤ n + 1 = d`.
  have hd1 : Module.finrank κ V = n + 1 := by omega
  rw [hd, hd1]
  omega

/-! ## Theorem 2 — a regular local ring of any dimension is a domain (Stacks 00NP) -/

/-- Cancel `+ 1` in `WithBot ℕ∞` against a natural-number successor: if `a + 1 = ↑(e+1)` then
`a = ↑e`. Used to read off `dim (R/(x)) = e` from the parameter dimension-drop. -/
private theorem withBot_eNat_add_one_cancel {a : WithBot ℕ∞} {e : ℕ}
    (h : a + 1 = ((e + 1 : ℕ) : WithBot ℕ∞)) : a = ((e : ℕ) : WithBot ℕ∞) := by
  induction a with
  | bot => exact absurd h.symm (by simp)
  | coe b =>
    induction b with
    | top =>
      exfalso
      have hb : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = (⊤ : WithBot ℕ∞) := by rw [WithBot.coe_top]; rfl
      rw [hb] at h
      have hlt : ((e + 1 : ℕ) : WithBot ℕ∞) < ⊤ := by
        rw [← WithBot.coe_top]
        exact_mod_cast WithBot.coe_lt_coe.mpr (by exact_mod_cast (ENat.coe_lt_top (e + 1)))
      exact (lt_irrefl _ (h ▸ hlt))
    | coe k =>
      have hke : k + 1 = e + 1 := by exact_mod_cast h
      have hk : k = e := by omega
      rw [hk]; norm_cast

/-- **Auxiliary form for the induction.** A regular local ring whose embedding dimension equals a
fixed natural number `d` is a domain. Strong induction on `d`; the ring `R` is universally
quantified so the inductive step may pass to `R ⧸ (x)`. -/
theorem isDomain_of_isRegularLocalRing_aux :
    ∀ (d : ℕ) (R : Type*) [CommRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = d → IsDomain R := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro R _ _ hdR
    match d, hdR with
    | 0, hdR =>
      -- base case: `spanFinrank 𝔪 = 0 ⇒ 𝔪 = ⊥ ⇒ field ⇒ domain`.
      have hbot : maximalIdeal R = ⊥ := by
        rw [← Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _), hdR]
      have hfield : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot
      exact hfield.toField.isDomain
    | (e + 1), hdR =>
      -- `dim R = ↑(e+1)`, so `m.height = e+1 ≥ 1`; `m ∉ minimalPrimes`.
      have hdim : ringKrullDim R = ((e + 1 : ℕ) : WithBot ℕ∞) := by
        have := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
        rw [hdR] at this; exact this.symm
      -- `¬ m ≤ m²`: else Nakayama gives `m = ⊥`, so `R` is a field with `spanFinrank = 0`.
      have hmsq : ¬ (maximalIdeal R ≤ (maximalIdeal R) ^ 2) := by
        intro hle
        have hmbot : maximalIdeal R = ⊥ := by
          apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
            (IsNoetherian.noetherian _)
          · rw [smul_eq_mul, ← pow_two]; exact hle
          · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
        rw [hmbot] at hdR
        simp at hdR
      -- `m` itself is not a minimal prime: `m.height = e+1 ≥ 1 ≠ 0`.
      have hm_not_min : maximalIdeal R ∉ minimalPrimes R := by
        intro hmem
        have h0 : (maximalIdeal R).primeHeight = 0 := Ideal.primeHeight_eq_zero_iff.mpr hmem
        have hh : (maximalIdeal R).height = ringKrullDim R :=
          IsLocalRing.maximalIdeal_height_eq_ringKrullDim
        rw [Ideal.height_eq_primeHeight, h0, hdim] at hh
        -- `(↑0 : WithBot ℕ∞) = ↑(e+1)` is impossible.
        exact absurd (by exact_mod_cast hh : (0 : ℕ) = e + 1) (by omega)
      -- each minimal prime `p` does not contain `m` (else `p = m`, so `m` would be minimal).
      have hm_not_le : ∀ p ∈ minimalPrimes R, ¬ (maximalIdeal R ≤ p) := by
        intro p hp hle
        have hpprime : p.IsPrime := Ideal.minimalPrimes_isPrime hp
        have : maximalIdeal R = p :=
          (maximalIdeal.isMaximal R).eq_of_le hpprime.ne_top hle
        rw [this] at hm_not_min
        exact hm_not_min hp
      -- **prime avoidance**: find `x ∈ m`, `x ∉ m²`, `x ∉ p` for all minimal primes `p`.
      have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
      haveI : Finite (minimalPrimes R) := hfin
      -- index family over `Option (minimalPrimes R)`: `none ↦ m²`, `some p ↦ p`.
      classical
      set f : Option (minimalPrimes R) → Ideal R :=
        fun o => o.elim ((maximalIdeal R) ^ 2) (fun p => (p : Ideal R)) with hf
      have hsfin : (Set.univ : Set (Option (minimalPrimes R))).Finite := Set.finite_univ
      have hprime : ∀ i ∈ (Set.univ : Set (Option (minimalPrimes R))),
          i ≠ none → i ≠ none → (f i).IsPrime := by
        rintro (_ | p) _ hne _
        · exact absurd rfl hne
        · exact Ideal.minimalPrimes_isPrime p.2
      -- `m ⊄ ⋃ i, f i`.
      have hnotsub : ¬ ((maximalIdeal R : Set R) ⊆ ⋃ i ∈ (Set.univ : Set (Option _)), f i) := by
        rw [Ideal.subset_union_prime_finite hsfin none none hprime]
        rintro ⟨(_ | p), _, hle⟩
        · exact hmsq hle
        · exact hm_not_le p p.2 hle
      -- extract the witness `x`.
      obtain ⟨x, hxm, hxnot⟩ := Set.not_subset.mp hnotsub
      have hxm2 : x ∉ (maximalIdeal R) ^ 2 := by
        intro hc
        exact hxnot (Set.mem_biUnion (Set.mem_univ (none : Option _)) (by rw [hf]; exact hc))
      have hxp : ∀ p ∈ minimalPrimes R, x ∉ p := by
        intro p hp hc
        exact hxnot (Set.mem_biUnion (Set.mem_univ (some ⟨p, hp⟩)) (by rw [hf]; exact hc))
      -- ----- `R ⧸ (x)` is a local Noetherian ring -----
      have hspanx_ne_top : Ideal.span {x} ≠ ⊤ := by
        rw [Ne, Ideal.span_singleton_eq_top]
        exact fun hu => (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ hxm hu)
      haveI : Nontrivial (R ⧸ Ideal.span {x}) :=
        Ideal.Quotient.nontrivial_iff.mpr hspanx_ne_top
      haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
          Ideal.Quotient.mk_surjective
      -- ----- embedding-dimension drop (Theorem 1): `spanFinrank 𝔪(R/(x)) ≤ e` -----
      have hdrop : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤ e + 1 := by
        rw [← hdR]
        exact spanFinrank_maximalIdeal_quotient_span_singleton_add_one_le hxm hxm2
      have hspanle : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ e := by omega
      -- ----- dimension drop: `ringKrullDim (R/(x)) = ↑e` -----
      have hdimdrop : ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
        have hinj : Function.Injective (algebraMap R R) := fun {a b} h => h
        have hann : ∀ p ∈ (Module.annihilator R R).minimalPrimes, x ∉ p := by
          have hb : Module.annihilator R R = ⊥ :=
            Module.annihilator_eq_bot.mpr
              ((faithfulSMul_iff_algebraMap_injective R R).mpr hinj)
          rw [hb]; intro p hp; exact hxp p hp
        have hkey :=
          Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
            (M := R) hann hxm
        rw [Module.supportDim_self_eq_ringKrullDim] at hkey
        have he : x • (⊤ : Submodule R R) = Ideal.span {x} := by
          rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
        have hbridge : Module.supportDim R (QuotSMulTop x R)
            = ringKrullDim (R ⧸ Ideal.span {x}) := by
          rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq (x • (⊤ : Submodule R R))
            (Ideal.span {x}) he), Module.supportDim_quotient_eq_ringKrullDim]
        rw [hbridge] at hkey; exact hkey
      have hdimE : ringKrullDim (R ⧸ Ideal.span {x}) = ((e : ℕ) : WithBot ℕ∞) := by
        rw [hdim] at hdimdrop
        exact withBot_eNat_add_one_cancel hdimdrop
      -- ----- `R ⧸ (x)` is regular of dimension `e` -----
      haveI : IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
        apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
        rw [hdimE]
        exact_mod_cast hspanle
      -- ----- by strong induction, `R ⧸ (x)` is a domain, so `(x)` is prime -----
      haveI : IsDomain (R ⧸ Ideal.span {x}) :=
        IH (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank (by omega)
          (R ⧸ Ideal.span {x}) rfl
      have hIprime : (Ideal.span {x}).IsPrime :=
        (Ideal.Quotient.isDomain_iff_prime (Ideal.span {x})).mp inferInstance
      -- ----- Nakayama finish: a minimal prime `q ≤ (x)` is `⊥`, so `R` is a domain -----
      obtain ⟨q, hqmin, hqle⟩ := Ideal.exists_minimalPrimes_le (J := Ideal.span {x}) bot_le
      haveI hqprime : q.IsPrime := Ideal.minimalPrimes_isPrime hqmin
      have hxnotq : x ∉ q := hxp q hqmin
      have hstep : q ≤ (maximalIdeal R) • q := by
        intro y hy
        have hyspan : y ∈ Ideal.span {x} := hqle hy
        rw [Ideal.mem_span_singleton] at hyspan
        obtain ⟨c, rfl⟩ := hyspan
        have hc : c ∈ q := by
          rcases hqprime.mem_or_mem hy with h | h
          · exact absurd h hxnotq
          · exact h
        exact Submodule.smul_mem_smul hxm hc
      have hqbot : q = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) q
          (IsNoetherian.noetherian _) hstep
          (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
      haveI : (⊥ : Ideal R).IsPrime := hqbot ▸ hqprime
      exact IsDomain.of_bot_isPrime R

/-- **A regular local ring of any dimension is a domain** (Stacks 00NP). -/
theorem isDomain_of_isRegularLocalRing
    {R : Type*} [CommRing R] [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_isRegularLocalRing_aux (IsLocalRing.maximalIdeal R).spanFinrank R rfl

end JacobianAlggeo
