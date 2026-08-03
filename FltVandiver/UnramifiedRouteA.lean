import FltRegular.NumberTheory.KummersLemma.Field
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import CyclotomicNT.PrimitiveRootUnit
import CyclotomicNT.UnramifiedDescent

/-!
# `isUnramified_routeA_elt` — element-level Kummer unramifiedness

This file gives the axiom-free proof of C4 (`isUnramified_routeA_elt`) in
`FltVandiver/RouteA.lean`,
which asserts that for the descent's minus element `u = routeAElt ζ x y` (a genuine fraction
in `K = ℚ(ζ_p)`), the Kummer extension `K(u^{1/p})` is unramified over `𝓞 K`.

## Why this is hard

`flt-regular`'s `KummersLemma.isUnramified` (`FltRegular.NumberTheory.KummersLemma.Field`)
proves the unramified statement for a **unit** `u : (𝓞 K)ˣ` with `(ζ-1)^p ∣ u - 1`. The key
step is `separable_poly_aux` (lines 227+ in that file): showing that the polynomial
`(C (ζ-1) * X - 1)^p + C u`, divided by `(ζ-1)^p`, becomes separable modulo any prime of `𝓞 L`.
The proof factors over `L` as a product of `(X - polyRoot ...)` terms, and shows pairwise
coprimality of those linear factors by exhibiting their differences as **units** in `𝓞 L`.
This unit-essentiality is the load-bearing place where the proof breaks for our `u`.

Our `u = routeAElt ζ x y = (-ζ⁻¹)·(x+ζy)/(x+ζ⁻¹y)` is **not in `𝓞 K`** (the denominator
`x+ζ⁻¹y` need not be a unit), and `u^{1/p}` is not a unit in `𝓞 L` either: its `q`-adic
valuation is `v_q(u)/p`, which is nonzero at primes dividing the support of `(u)`.

## The two local cases

The original 3-case decomposition (a)/(b)/(c) **collapses to 2 cases** by using a different
integral generator at primes `I ≠ 𝔭`. Cases (b) and (c) unify into a single "good prime" case
via a coordinate-free trick: pick `d ∈ K` with `v_I(d) = -v_I(u)/p` and use `γ = d · α` as the
integral generator, with minimal polynomial `X^p - C(u · d^p)` over `K`. This avoids choosing
uniformizers and gives separability mod `I` directly from the derivative test (since residue
char ≠ `p` for `I ≠ 𝔭`).

**Both cases need denominator-clearing.**
`α = u^{1/p}` is NOT globally integral (`v_𝔓(α) = v_q(J) < 0` at primes in the support of `J`),
so neither is the shifted `β = (1-α)/(ζ-1)`. Mathlib's `isUnramifiedAt_of_Separable_minpoly`
requires a **globally integral** generator, so even case A at `𝔭` must clear denominators —
NOT just case B. The fix is a class-group-free fractional-ideal trick (see "The linchpin" below).

* **Case A — `I = 𝔭` (the wild prime).** Need a multiplier `c ∈ K` making `γ := c·α` globally
  integral (`c ∈ J⁻¹`) AND preserving the congruence `γ^p ≡ 1 mod 𝔭^p` (so that the shifted
  polynomial `polyElement` / `polyRootElement` machinery applies). For the latter it suffices
  that `c ≡ 1 mod 𝔭` (then `c^p ≡ 1 mod 𝔭^p`, and `γ^p = c^p·u ≡ 1·1 = 1 mod 𝔭^p`).
  Construction: pick `a ∈ J \ J𝔭`; `A := a·J⁻¹` is integral (`a ∈ J`) and coprime to `𝔭`
  (`a ∉ J𝔭`); `A + 𝔭 = 𝓞_K` ⟹ `∃ x ∈ A, y ∈ 𝔭, x + y = a`; set `c = x/a`. Then `x ∈ A =
  a·J⁻¹` ⟹ `c ∈ J⁻¹` (integral); `c = 1 - y/a` with `v_𝔭(y) ≥ 1`, `v_𝔭(a) = 0` ⟹ `c ≡ 1
  mod 𝔭`. Then `β = (γ-1)/(ζ-1)` is globally integral and the shifted-polynomial separability
  argument applies (the `separable_poly_aux_element` family, with `γ^p` in place of `a`).

* **Case B — `I ≠ 𝔭` (any other prime).** Need `d ∈ K` making `γ := d·α` globally integral
  (`d ∈ J⁻¹`) with `v_I(d) = -v_I(J)` exactly (so `u' := γ^p = u·d^p` is an `I`-unit).
  Construction: pick `d ∈ J⁻¹ \ J⁻¹·I` (exists by the linchpin below). Then `d ∈ J⁻¹` ⟹ `γ`
  globally integral; `d ∉ J⁻¹·I` ⟹ `v_I(d) = -v_I(J)` exactly ⟹ `v_I(u') = 0` ⟹ `u'` an
  `I`-unit. Minimal polynomial `X^p - C u'`, separable mod `I` by the derivative test
  (residue char ≠ `p`, `u'` an `I`-unit) — this is the already-shipped
  `separable_X_pow_sub_C_modI`. **No shifted polynomial trick needed.**

Both cases feed `isUnramifiedAt_of_Separable_minpoly` (from flt-regular's `Unramified.lean`)
with their per-prime generator and separability witness; the global `IsUnramified` follows.

### The linchpin (class-group-free generator existence)

The key elementary fact (no class group, no CRT): for an **invertible** fractional ideal `J⁻¹`
and a **proper** ideal `I ⊊ 𝓞_K`, we have a strict inclusion `J⁻¹·I ⊊ J⁻¹` (multiply `I ⊊ 1`
by the invertible `J⁻¹`). Hence `J⁻¹ \ J⁻¹·I ≠ ∅` — an element `d` with `d ∈ J⁻¹` (global
integrality of `d·α`) and `d ∉ J⁻¹·I` (exact `I`-valuation, giving the `I`-unit). The case-A
multiplier `c` comes from the same trick applied to `J \ J𝔭` plus the coprimality
`A + 𝔭 = 𝓞_K`.

### Why no SINGLE global generator works for all primes

There is no single integral `γ ∈ 𝓞 L` whose minimal polynomial is separable mod every prime
of `𝓞 K`. The fractional ideal `(α) = 𝔍 · 𝓞 L` is genuinely `𝔍`-divisible, so to make `α`
integral globally we'd need `(c) = 𝔍^{-1}` in `K` — only possible if `𝔍` is principal. Even
then, the minimal polynomial wouldn't be separable at primes dividing `𝔍`. So the per-prime
generator switch is mathematically fundamental — but each per-prime generator IS globally
integral (that's the point of the linchpin); it's just that no single one works everywhere.

### No Mathlib shortcut

Mathlib has the API for prescribed valuations and per-prime unramifiedness
(`isUnramifiedAt_of_Separable_minpoly`), but not the Kummer-theoretic / class-field-theoretic
shortcut "`(u) = J^p` ⟹ `K(u^{1/p})/K` unramified outside `p · disc`". So the explicit
per-prime polynomial separability above is the idiomatic Mathlib path.

## The pieces

1. **`zeta_sub_one_pow_dvd_poly_element`** — the polynomial-arithmetic step generalized from
   flt-regular's `zeta_sub_one_pow_dvd_poly` from unit `u : (𝓞 K)ˣ` to element `a : 𝓞 K` with
   the same `(ζ-1)^p ∣ a - 1` hypothesis. (The flt-regular proof never actually uses the
   unitness of `u` — only the congruence and the integrality of `u` as a coefficient of `C u`.)
   This is the wild-prime-case polynomial identity for an element instead of a unit,
   feeding `polyElement` and the `separable_poly` analog for case (a).

The pieces (all proven in this file):

2. `polyElement` family — element-form ports of flt-regular's `poly` / `monic_poly` /
   `natDegree_poly` / `map_poly` (lines 58–104 of `KummersLemma.Field`).

3. `polyRootElement` / `aeval_poly_element` / `roots_poly_element` / `splits_poly_element`
   / `map_poly_element_eq_prod` / `minpoly_polyRoot_element'` / `irreducible_map_poly_element`.

4. `separable_poly_aux_element` — replaces flt-regular's `separable_poly_aux` with a
   version where "α is a unit in `𝓞 L`" is an EXPLICIT hypothesis (`hα_unit`) rather than
   derived from `u.isUnit`, discharged locally per the case-A argument below.

5. `separable_X_pow_sub_C_modI` — for `(n:R) ∉ I` and `u' ∉ I`,
   `X^n - C u'` is separable mod `I`. The Case-B separability ingredient.

6. **Linchpin** `exists_mem_inv_not_mem_inv_mul` — for an invertible
   fractional ideal `Jinv` and proper ideal `I ⊊ 𝓞_K`, `∃ d, d ∈ Jinv ∧ d ∉ Jinv · I`.

7. **Case B abstract core** — `minpoly_eq_X_pow_sub_C_of_pth_root`
   (`γ^n = u'` ⟹ `minpoly 𝓞K γ = X^n - C u'`) + `isUnramifiedAt_of_pth_root` (bundles minpoly
   + `separable_X_pow_sub_C_modI` + `isUnramifiedAt_of_Separable_minpoly`). Parameterized over
   the generator `γ` and `u'`.

7b. **Case B concrete** (`isUnramifiedAt_caseB`) — from `α^p = u`, `(u) = J^p`, `u` not a
   `p`-th power, `adjoin K {α} = ⊤`: at every maximal `I` with `(p:𝓞K) ∉ I`, `𝓞 L/𝓞 K` is
   unramified at `I`. `γ = d·α` is integral **for free**
   from `γ^p = u' ∈ 𝓞 K` (root of monic `X^p - C u'`) — NO valuation↔fractional-ideal bridge
   needed. `u' = u·d^p` an `I`-unit integer from `exists_isInteger_isUnit_of_linchpin`;
   `X^p - C u'` irreducible since `u'` not a `p`-th power; closes via `isUnramifiedAt_of_pth_root`.

8. **Case A** `separable_at_pi` — pick `a ∈ J \ J𝔭`, form `A = a·J⁻¹` (integral, 𝔭-coprime),
   solve `x + y = a` (`x ∈ A`, `y ∈ 𝔭`) from `A + 𝔭 = ⊤`, set `c = x/a ∈ J⁻¹` with `c ≡ 1
   mod 𝔭`; `γ = c·α` globally integral, `γ^p ≡ 1 mod 𝔭^p`; feed `γ^p` (in place of `a`) to
   the `polyElement` / `separable_poly_aux_element` machinery (the `hα_unit` hypothesis of
   `separable_poly_aux_element` is discharged mod 𝔓 because `γ^p` is a 𝔭-unit).

9. Aggregate `isUnramified_element`: dispatch per maximal `I` to Case A (`I = 𝔭`) or Case B
   (`I ≠ 𝔭`); package as the discharge of `isUnramified_routeA_elt`.

## Naming convention

Throughout this file, `_element` suffix denotes the generalization of an existing
`flt-regular`/`KummersLemma.Field` definition from `u : (𝓞 K)ˣ` to `a : 𝓞 K`. -/

open scoped NumberField
open Polynomial

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : 𝓞 K)
  (hcong : (hζ.unit' - 1 : 𝓞 K) ^ p ∣ a - 1)

include hp hcong in
/-- **Element-form shifted polynomial identity.** For any algebraic integer `a : 𝓞 K` with
`(ζ - 1)^p ∣ a - 1` (no unit assumption), the polynomial `(C (ζ-1) * X - 1)^p + C a` is divisible
by `C ((ζ-1)^p)` in `(𝓞 K)[X]`. This is `flt-regular`'s `KummersLemma.zeta_sub_one_pow_dvd_poly`
with the hypothesis `u : (𝓞 K)ˣ` relaxed to `a : 𝓞 K`. The flt-regular proof doesn't actually
use the unitness — only the cast `(u : 𝓞 K) - 1` and the congruence, both of which carry over
verbatim. -/
lemma zeta_sub_one_pow_dvd_poly_element [IsCyclotomicExtension {p} ℚ K] :
    C ((hζ.unit' - 1 : 𝓞 K) ^ p) ∣
      (C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ p + C a := by
  rw [← dvd_sub_left (_root_.map_dvd C hcong), add_sub_assoc, C.map_sub a, ← sub_add,
    sub_self, map_one, zero_add]
  refine dvd_C_mul_X_sub_one_pow_add_one hpri.out hp _ _ dvd_rfl ?_
  convert mul_dvd_mul_right (associated_zeta_sub_one_pow_prime hζ).dvd _
  simp only [IsPrimitiveRoot.coe_unit']
  rw [← pow_succ, tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]

variable [IsCyclotomicExtension {p} ℚ K]

omit [IsCyclotomicExtension {p} ℚ K] in
omit [NumberField K] in
/-- `natDegree` of the unshifted polynomial. Element-form analog of
`KummersLemma.natDegree_poly_aux` (the flt-regular version states it specifically for
`C ↑u`; identical proof for an arbitrary element). -/
lemma natDegree_poly_aux_element :
    natDegree ((C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ p + C a) = p := by
  haveI : Fact (Nat.Prime p) := hpri
  rw [natDegree_add_C, natDegree_pow, ← C.map_one, natDegree_sub_C, natDegree_mul_X, natDegree_C,
    zero_add, mul_one]
  exact C_ne_zero.mpr (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)

omit [IsCyclotomicExtension {p} ℚ K] in
omit [NumberField K] in
/-- `leadingCoeff` of the unshifted polynomial. Element-form analog of
`KummersLemma.monic_poly_aux`. -/
lemma monic_poly_aux_element :
    leadingCoeff ((C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ p + C a) =
      (hζ.unit' - 1 : 𝓞 K) ^ p := by
  haveI : Fact (Nat.Prime p) := hpri
  trans leadingCoeff ((C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ p)
  · rw [leadingCoeff, leadingCoeff, coeff_add]
    nth_rewrite 1 [natDegree_add_C]
    convert add_zero _ using 2
    rw [natDegree_poly_aux_element hζ a, coeff_C, if_neg (NeZero.pos p).ne.symm]
  · rw [leadingCoeff_pow, ← C.map_one, leadingCoeff, natDegree_sub_C, natDegree_mul_X]
    · simp only [map_one, natDegree_C, zero_add, coeff_sub, coeff_mul_X, coeff_C, coeff_one,
        sub_zero, one_ne_zero, ↓reduceIte]
    · exact C_ne_zero.mpr (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)

/-- The polynomial `Q` extracted from `zeta_sub_one_pow_dvd_poly_element`:
`(ζ-1)^p · Q(X) = ((ζ-1)X - 1)^p + C a`. Element-form mirror of `flt-regular`'s
`KummersLemma.poly`. -/
noncomputable def polyElement : (𝓞 K)[X] :=
  (zeta_sub_one_pow_dvd_poly_element hp hζ a hcong).choose

include hp hcong in
/-- Defining equation of `polyElement`. -/
lemma poly_element_spec :
    C ((hζ.unit' - 1 : 𝓞 K) ^ p) * polyElement hp hζ a hcong =
      (C (hζ.unit' - 1 : 𝓞 K) * X - 1) ^ p + C a :=
  (zeta_sub_one_pow_dvd_poly_element hp hζ a hcong).choose_spec.symm

include hp hcong in
/-- `polyElement` is monic. -/
lemma monic_poly_element : Monic (polyElement hp hζ a hcong) := by
  haveI : Fact (Nat.Prime p) := hpri
  have := congr_arg leadingCoeff (poly_element_spec hp hζ a hcong)
  simp only [map_pow, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_C,
    monic_poly_aux_element hζ a] at this
  refine mul_right_injective₀ ?_ (this.trans (mul_one _).symm)
  exact pow_ne_zero _ (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)

include hp hcong in
/-- `polyElement` has degree `p`. -/
lemma natDegree_poly_element : natDegree (polyElement hp hζ a hcong) = p := by
  haveI : Fact (Nat.Prime p) := hpri
  have := congr_arg natDegree (poly_element_spec hp hζ a hcong)
  rwa [natDegree_C_mul, natDegree_poly_aux_element hζ a] at this
  exact pow_ne_zero _ (hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt)

include hp hcong in
/-- The image of `polyElement` in `K[X]`. Element-form analog of `flt-regular`'s `map_poly`,
where `(u : K)` is replaced by `(algebraMap (𝓞 K) K a)`. Same proof. -/
lemma map_poly_element : (polyElement hp hζ a hcong).map (algebraMap (𝓞 K) K) =
    (X - C (1 / (ζ - 1))) ^ p + C ((algebraMap (𝓞 K) K a) / (ζ - 1) ^ p) := by
  ext i
  have := congr_arg (fun P : (𝓞 K)[X] ↦ (↑(coeff P i) : K))
    (poly_element_spec hp hζ a hcong)
  change _ = algebraMap (𝓞 K) K _ at this
  rw [← coeff_map] at this
  replace this : (ζ - 1) ^ p * ↑((polyElement hp hζ a hcong).coeff i) =
      (((C ((algebraMap ((𝓞 K)) K) ↑hζ.unit') - 1) * X - 1) ^ p).coeff i +
      (C ((algebraMap ((𝓞 K)) K) a)).coeff i := by
    simp only [map_pow, map_sub, map_one, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_mul, map_C,
      Polynomial.map_one, map_X, coeff_add] at this
    convert this
    simp only [← Polynomial.coeff_map]
    simp only [coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C,
      Polynomial.map_one]
    rw [← Polynomial.coeff_map, mul_comm, ← Polynomial.coeff_mul_C, mul_comm]
    simp [show hζ.unit'.1 = ζ from rfl]
  apply mul_right_injective₀ (pow_ne_zero p (hζ.sub_one_ne_zero hpri.out.one_lt))
  simp only [coeff_map, one_div, coeff_add, this, mul_add]
  simp_rw [← smul_eq_mul (α := K), ← coeff_smul, show hζ.unit'.1 = ζ from rfl]
  rw [smul_C, smul_eq_mul, ← _root_.smul_pow, ← mul_div_assoc, mul_div_cancel_left₀, smul_sub,
    smul_C, smul_eq_mul, mul_inv_cancel₀, map_one, Algebra.smul_def, ← C_eq_algebraMap, map_sub,
    map_one]
  · exact hζ.sub_one_ne_zero hpri.out.one_lt
  · exact pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt)

include hp hcong in
/-- Element-form analog of `KummersLemma.irreducible_map_poly`: `polyElement` mapped to `K[X]`
is irreducible, provided `a` (viewed in `K`) is not a `p`-th power in `K`. -/
lemma irreducible_map_poly_element (ha : ∀ v : K, v ^ p ≠ algebraMap (𝓞 K) K a) :
    Irreducible ((polyElement hp hζ a hcong).map (algebraMap (𝓞 K) K)) := by
  rw [map_poly_element]
  refine Irreducible.of_map (f := algEquivAevalXAddC (1 / (ζ - 1))) ?_
  simp only [one_div, map_add, algEquivAevalXAddC_apply, map_pow, map_sub, aeval_X, aeval_C,
    algebraMap_eq, add_sub_cancel_right]
  rw [← sub_neg_eq_add, ← (C : K →+* _).map_neg]
  apply X_pow_sub_C_irreducible_of_prime hpri.out
  intro b hb
  apply ha (- b * (ζ - 1))
  rw [mul_pow, (hpri.out.odd_of_ne_two hp).neg_pow, hb, neg_neg,
    div_mul_cancel₀ _ (pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt))]

include hp hcong in
/-- Element-form analog of `KummersLemma.aeval_poly`: every `(1 - ζ^m · α)/(ζ - 1)`
(for `α` any `p`-th root of `algebraMap (𝓞 K) K a` in an extension `L`) is a root of
`polyElement` in `L`. -/
theorem aeval_poly_element {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap (𝓞 K) L a) (m : ℕ) :
    aeval (((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1))) (polyElement hp hζ a hcong) = 0 := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_sub, map_one]
  have := congr_arg (aeval ((1 - ζ ^ m • α) / (algebraMap K L (ζ - 1))))
    (poly_element_spec hp hζ a hcong)
  have hcoe : (algebraMap (𝓞 K) L) (↑hζ.unit') = algebraMap K L ζ := rfl
  simp only [map_sub, map_one, map_pow, map_mul, aeval_C, _root_.smul_pow, hcoe, e, map_add,
    aeval_X, ← mul_div_assoc, mul_div_cancel_left₀ _ hζ', sub_sub_cancel_left,
    (hpri.out.odd_of_ne_two hp).neg_pow] at this
  rw [← pow_mul, mul_comm m, pow_mul, hζ.pow_eq_one, one_pow, one_smul, neg_add_cancel,
    mul_eq_zero] at this
  exact this.resolve_left (pow_ne_zero _ hζ')

/-- Element-form analog of `KummersLemma.polyRoot`: the integral element
`(1 - ζ^m · α)/(ζ - 1) ∈ 𝓞 L`. -/
noncomputable def polyRootElement {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap (𝓞 K) L a) (m : ℕ) : 𝓞 L :=
  ⟨((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1)), isIntegral_trans _
    ⟨polyElement hp hζ a hcong, monic_poly_element hp hζ a hcong,
     aeval_poly_element hp hζ a hcong α e m⟩⟩

include hp hcong in
/-- Element-form analog of `KummersLemma.roots_poly`. The roots of `polyElement` (lifted to `L`)
are the `p` values `polyRootElement ... α e i`, `i = 0, ..., p-1`. The unit-essential step in
`flt-regular` is replaced by `ha : a ≠ 0` (which is enough to rule out `α = 0`). -/
theorem roots_poly_element (ha : a ≠ 0)
    {L : Type*} [Field L] [Algebra K L] (α : L) (e : α ^ p = algebraMap (𝓞 K) L a) :
    roots ((polyElement hp hζ a hcong).map (algebraMap (𝓞 K) L)) =
      (Finset.range p).val.map
        (fun i ↦ ((1 : L) - ζ ^ i • α) / (algebraMap K L (ζ - 1))) := by
  by_cases hα : α = 0
  · -- α = 0 ⟹ α^p = 0 ⟹ algebraMap (𝓞 K) L a = 0. Since a ≠ 0 and algebraMap (𝓞 K) L
    -- factors through K (which is a field), algebraMap (𝓞 K) L a ≠ 0 — contradiction.
    rw [hα, zero_pow (NeZero.ne p)] at e
    have h1 : Function.Injective (algebraMap (𝓞 K) K) :=
      FaithfulSMul.algebraMap_injective _ _
    have h2 : Function.Injective (algebraMap K L) := (algebraMap K L).injective
    have h3 : Function.Injective (algebraMap (𝓞 K) L) := by
      rw [IsScalarTower.algebraMap_eq (𝓞 K) K L]
      exact h2.comp h1
    exact absurd (h3 (by simpa using e.symm)) ha
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  classical
  symm; apply Multiset.eq_of_le_of_card_le
  · rw [← Finset.image_val_of_injOn, Finset.val_le_iff_val_subset]
    · intro x hx
      simp only [Finset.image_val, Finset.range_val, Multiset.mem_dedup, Multiset.mem_map,
        Multiset.mem_range] at hx
      obtain ⟨m, _, rfl⟩ := hx
      rw [mem_roots, IsRoot.def, eval_map, ← aeval_def, aeval_poly_element hp hζ a hcong α e]
      exact ((monic_poly_element hp hζ a hcong).map (algebraMap (𝓞 K) L)).ne_zero
    · intros i hi j hj e
      apply (hζ.map_of_injective (algebraMap K L).injective).injOn_pow_mul hα hi hj
      apply_fun (1 - · * (algebraMap K L ζ - 1)) at e
      dsimp only at e
      simpa only [Nat.cast_one, map_sub, map_one, Algebra.smul_def, map_pow,
        div_mul_cancel₀ _ hζ', sub_sub_cancel] using e
  · simp only [Finset.range_val, Multiset.card_map, Multiset.card_range]
    refine (Polynomial.card_roots' _).trans ?_
    rw [(monic_poly_element hp hζ a hcong).natDegree_map, natDegree_poly_element hp hζ]

include hp hcong in
/-- Element-form analog of `KummersLemma.splits_poly`. -/
theorem splits_poly_element (ha : a ≠ 0)
    {L : Type*} [Field L] [Algebra K L] (α : L) (e : α ^ p = algebraMap (𝓞 K) L a) :
    ((polyElement hp hζ a hcong).map (algebraMap (𝓞 K) L)).Splits := by
  rw [splits_iff_card_roots, roots_poly_element hp hζ a hcong ha α e,
    (monic_poly_element hp hζ a hcong).natDegree_map, natDegree_poly_element hp hζ,
    Finset.range_val, Multiset.card_map, Multiset.card_range]

include hp hcong in
/-- Element-form analog of `KummersLemma.map_poly_eq_prod`. -/
theorem map_poly_element_eq_prod (ha : a ≠ 0)
    {L : Type*} [Field L] [Algebra K L] (α : L) (e : α ^ p = algebraMap (𝓞 K) L a) :
    (polyElement hp hζ a hcong).map (algebraMap (𝓞 K) (𝓞 L)) =
      ∏ i ∈ Finset.range p, (X - C (polyRootElement hp hζ a hcong α e i)) := by
  apply map_injective (algebraMap (𝓞 L) L) Subtype.coe_injective
  rw [← coe_mapRingHom, map_prod, coe_mapRingHom, map_map, ← IsScalarTower.algebraMap_eq,
    (splits_poly_element hp hζ a hcong ha α e).eq_prod_roots_of_monic
      ((monic_poly_element hp hζ a hcong).map _),
    roots_poly_element hp hζ a hcong ha α e, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  simp [polyRootElement]

include hp hcong in
/-- Element-form analog of `KummersLemma.minpoly_polyRoot''`. -/
lemma minpoly_polyRoot_element'' (ha_npow : ∀ v : K, v ^ p ≠ algebraMap (𝓞 K) K a)
    {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap (𝓞 K) L a) (i) :
    minpoly K (polyRootElement hp hζ a hcong α e i : L) =
      (polyElement hp hζ a hcong).map (algebraMap (𝓞 K) K) := by
  have : IsIntegral K (polyRootElement hp hζ a hcong α e i : L) :=
    IsIntegral.tower_top (polyRootElement hp hζ a hcong α e i).prop
  apply eq_of_monic_of_associated (minpoly.monic this) ((monic_poly_element hp hζ a hcong).map _)
  refine Irreducible.associated_of_dvd (minpoly.irreducible this)
    (irreducible_map_poly_element hp hζ a hcong ha_npow) (minpoly.dvd _ _ ?_)
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq, ← aeval_def]
  exact aeval_poly_element hp hζ a hcong α e i

include hp hcong in
/-- Element-form analog of `KummersLemma.minpoly_polyRoot'`. -/
lemma minpoly_polyRoot_element' (ha_npow : ∀ v : K, v ^ p ≠ algebraMap (𝓞 K) K a)
    {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap (𝓞 K) L a) (i) :
    minpoly (𝓞 K) (polyRootElement hp hζ a hcong α e i : L) = polyElement hp hζ a hcong := by
  apply map_injective (algebraMap (𝓞 K) K) Subtype.coe_injective
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K]
  · exact minpoly_polyRoot_element'' hp hζ a hcong ha_npow α e i
  · exact IsIntegral.tower_top (polyRootElement hp hζ a hcong α e i).prop

include hp hcong in
/-- **Root-difference identity.** For `i ≠ j` in `range p`, the difference of the two
`polyRootElement` roots is `(unit) · α`: concretely `βᵢ - βⱼ = (algebraMap v) · ⟨α,_⟩` for a
unit `v : (𝓞 K)ˣ` (the one witnessing `Associated (ζ-1) (ζʲ - ζⁱ)`). This is the load-bearing
identity inside `separable_poly_aux_element`, extracted so the **wild-prime (𝔭) residue-field**
separability can reuse it: there the differences need only be *nonzero mod 𝔔* (i.e. `α ∉ 𝔔`),
not global units. -/
lemma polyRoot_element_sub (_ha : a ≠ 0)
    {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap (𝓞 K) L a) (hα_int : IsIntegral (𝓞 K) α)
    {i j : ℕ} (hi : i ∈ Finset.range p) (hj : j ∈ Finset.range p) (hij : i ≠ j) :
    ∃ v : (𝓞 K)ˣ,
      polyRootElement hp hζ a hcong α e i - polyRootElement hp hζ a hcong α e j
        = algebraMap (𝓞 K) (𝓞 L) (v : 𝓞 K) * ⟨α, isIntegral_trans _ hα_int⟩ := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  obtain ⟨v, hv⟩ :
      Associated (hζ.unit' - 1 : 𝓞 K) ((hζ.unit' : 𝓞 K) ^ j - (hζ.unit' : 𝓞 K) ^ i) := by
    refine hζ.unit'_coe.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime hpri.out ?_ ?_ ?_
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.unit'_coe.pow_eq_one, one_pow]
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.unit'_coe.pow_eq_one, one_pow]
    · exact mt (hζ.unit'_coe.injOn_pow hj hi) hij.symm
  refine ⟨v, ?_⟩
  rw [NumberField.RingOfIntegers.ext_iff] at hv
  have hcoe : (algebraMap (𝓞 K) K) (↑hζ.unit') = ζ := rfl
  simp only [map_mul, map_sub, map_one, map_pow, hcoe] at hv
  ext
  simp only [polyRootElement, map_sub, map_one, sub_div, one_div, map_sub,
    sub_sub_sub_cancel_left, map_mul, NumberField.RingOfIntegers.map_mk]
  rw [← sub_div, ← sub_smul, ← hv, Algebra.smul_def, map_mul, map_sub, map_one, mul_assoc,
    mul_div_cancel_left₀ _ hζ']
  rfl

include hp hcong in
/-- Element-form analog of `KummersLemma.polyRoot_spec`: `α` recovered from its shifted root
`β = polyRootElement … i` via `α = (ζⁱ)⁻¹ • (1 - (ζ-1) • β)`. -/
lemma polyRoot_element_spec {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap (𝓞 K) L a) (i) :
    α = (ζ ^ i)⁻¹ • (1 - (ζ - 1) • (polyRootElement hp hζ a hcong α e i : L)) := by
  apply smul_right_injective (M := L) (r := ζ ^ i) (pow_ne_zero _ <| hζ.ne_zero
    (NeZero.pos p).ne.symm)
  simp only [polyRootElement, map_sub, map_one, NumberField.RingOfIntegers.map_mk,
    Algebra.smul_def (ζ - 1), ← mul_div_assoc,
    mul_div_cancel_left₀ _
      ((hζ.map_of_injective (algebraMap K L).injective).sub_one_ne_zero hpri.out.one_lt),
    sub_sub_cancel, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ <| hζ.ne_zero (NeZero.pos p).ne.symm),
      one_smul]

include hp hcong in
/-- Element-form analog of `KummersLemma.mem_adjoin_polyRoot`: `α` lies in the `K`-subalgebra
generated by its shifted root `β = polyRootElement … i`. Hence `adjoin K {α} ≤ adjoin K {β}`,
which (with the reverse inclusion automatic) makes the shifted root a generator of `L`. -/
lemma mem_adjoin_polyRoot_element {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap (𝓞 K) L a) (i) :
    α ∈ Algebra.adjoin K {(polyRootElement hp hζ a hcong α e i : L)} := by
  conv => enter [2]; rw [polyRoot_element_spec hp hζ a hcong α e i]
  exact Subalgebra.smul_mem _ (sub_mem (one_mem _)
    (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton K _) _)) _

include hp hcong in
/-- **Wild-prime (𝔭) residue-field separability.** The shifted polynomial `polyElement`,
reduced modulo a maximal ideal `𝔔` of `𝓞 L`, is separable over the residue field `𝓞 L / 𝔔`,
provided only that the `p`-th root `α` is a `𝔔`-unit (`α ∉ 𝔔`). This is the wild-prime analog
of `separable_poly_aux_element`: there `α` had to be a *global* unit of `𝓞 L`; here it need only
avoid the single prime `𝔔` (which holds at `𝔭` because `α^p = a ≡ 1 mod 𝔭^p` makes `a`, hence
`α`, a `𝔭`-unit). The roots `βᵢ = (1 - ζⁱα)/(ζ-1)` stay distinct mod `𝔔` because their pairwise
differences are `(unit)·α` (`polyRoot_element_sub`), nonzero mod `𝔔` exactly when `α ∉ 𝔔`. -/
lemma separable_poly_element_mod (ha : a ≠ 0)
    {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap (𝓞 K) L a) (hα_int : IsIntegral (𝓞 K) α)
    (𝔔 : Ideal (𝓞 L)) [hQ : 𝔔.IsMaximal]
    (hα : (⟨α, isIntegral_trans _ hα_int⟩ : 𝓞 L) ∉ 𝔔) :
    Separable ((polyElement hp hζ a hcong).map
        ((Ideal.Quotient.mk 𝔔).comp (algebraMap (𝓞 K) (𝓞 L)))) := by
  letI : Field (𝓞 L ⧸ 𝔔) := Ideal.Quotient.field 𝔔
  haveI : 𝔔.IsPrime := hQ.isPrime
  rw [← Polynomial.map_map, map_poly_element_eq_prod hp hζ a hcong ha α e,
    ← Polynomial.coe_mapRingHom, map_prod]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  refine (separable_prod_X_sub_C_iff' (f := fun i => (Ideal.Quotient.mk 𝔔)
    (polyRootElement hp hζ a hcong α e i))).mpr ?_
  intro x hx y hy hxy
  by_contra hne
  -- `mk βₓ = mk βᵧ` ⟹ `βₓ - βᵧ ∈ 𝔔`; but `βₓ - βᵧ = (unit)·α`, so `α ∈ 𝔔` — contradiction.
  obtain ⟨v, hv⟩ := polyRoot_element_sub hp hζ a hcong ha α e hα_int hx hy hne
  have hsub : polyRootElement hp hζ a hcong α e x
      - polyRootElement hp hζ a hcong α e y ∈ 𝔔 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub,
      show (Ideal.Quotient.mk 𝔔) (polyRootElement hp hζ a hcong α e x)
        = (Ideal.Quotient.mk 𝔔) (polyRootElement hp hζ a hcong α e y) from hxy, sub_self]
  simp only [hv] at hsub
  have hvunit : IsUnit (algebraMap (𝓞 K) (𝓞 L) (v : 𝓞 K)) :=
    (algebraMap (𝓞 K) (𝓞 L)).isUnit_map v.isUnit
  rcases (Ideal.IsPrime.mem_or_mem ‹𝔔.IsPrime› hsub) with hv' | hα'
  · exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hv' hvunit)
  · exact hα hα'

include hp hcong in
/-- **Case A core (unramified at the wild prime `𝔭`).** Let `γ : L` generate `L/K`
(`adjoin K {γ} = ⊤`) with `γ^p = a` (the section integer `a`, satisfying `(ζ-1)^p ∣ a-1`), `γ`
integral over `𝓞 K`, and `a` not a `p`-th power in `K`. Then at any maximal ideal `𝔭` of `𝓞 K`
containing `ζ - 1` (the wild prime above `p`), the extension `𝓞 L / 𝓞 K` is unramified.

The generator's minimal polynomial is the **shifted** `polyElement` (not `X^p - C a`, which is
inseparable mod `𝔭`). Separability of `(minpoly 𝓞K β).map (mk 𝔭)` is obtained by lifting to a
maximal prime `𝔔` of `𝓞 L` lying over `𝔭`: there `separable_poly_element_mod` applies because
`γ` is a `𝔔`-unit (`γ^p = a ≡ 1 mod 𝔭`, so `a ∉ 𝔭` hence `γ ∉ 𝔔`), and the residue-field
embedding `𝓞 K/𝔭 ↪ 𝓞 L/𝔔` reflects separability via `Polynomial.separable_map`. -/
lemma isUnramifiedAt_caseA_core (ha_npow : ∀ v : K, v ^ p ≠ algebraMap (𝓞 K) K a)
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (γ : L) (e : γ ^ p = algebraMap (𝓞 K) L a)
    (hγ_int : IsIntegral (𝓞 K) γ)
    (hadj : Algebra.adjoin K {γ} = ⊤)
    (𝔭 : Ideal (𝓞 K)) [h𝔭max : 𝔭.IsMaximal]
    (hπ𝔭 : (hζ.unit' - 1 : 𝓞 K) ∈ 𝔭) :
    IsUnramifiedAt (𝓞 L) 𝔭 := by
  -- `ζ - 1 ≠ 0`, so `𝔭 ≠ ⊥`.
  have hπ_ne : (hζ.unit' - 1 : 𝓞 K) ≠ 0 := by
    intro h
    have h1 : algebraMap (𝓞 K) K (hζ.unit' - 1) = 0 := by rw [h]; simp
    rw [map_sub, map_one, (show (algebraMap (𝓞 K) K) (↑hζ.unit') = ζ from rfl),
      sub_eq_zero] at h1
    exact hζ.ne_one hpri.out.one_lt h1
  have h𝔭bot : 𝔭 ≠ ⊥ := by
    intro h; rw [h, Ideal.mem_bot] at hπ𝔭; exact hπ_ne hπ𝔭
  -- `a` is a `𝔭`-unit: `a - 1 ∈ (ζ-1)^p ⊆ 𝔭`, so `a ∉ 𝔭` (else `1 = a - (a-1) ∈ 𝔭`).
  have hπp𝔭 : (hζ.unit' - 1 : 𝓞 K) ^ p ∈ 𝔭 := Ideal.pow_mem_of_mem 𝔭 hπ𝔭 _ hpri.out.pos
  have ha_unit : a ∉ 𝔭 := by
    intro hmem
    obtain ⟨t, ht⟩ := hcong
    have ha1 : a - 1 ∈ 𝔭 := ht ▸ Ideal.mul_mem_right _ _ hπp𝔭
    have h1 : (1 : 𝓞 K) ∈ 𝔭 := by simpa using sub_mem hmem ha1
    exact h𝔭max.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have ha0 : a ≠ 0 := by rintro rfl; exact ha_unit (Ideal.zero_mem _)
  -- Reduce to unramifiedness at each prime `𝔔 ∣ 𝔭` of `𝓞 L`; `γ ∉ 𝔔` since `γ^p = a ∉ 𝔭`.
  apply isUnramifiedAt_of_forall_isUnramifiedAt h𝔭bot
  intro 𝔔 h𝔔prime h𝔔over
  letI := h𝔔prime
  letI : 𝔔.LiesOver 𝔭 := h𝔔over
  haveI : 𝔔.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔔) h𝔔prime
  have hcomap : Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) 𝔔 = 𝔭 := by
    rw [← Ideal.under_def]; exact h𝔔over.over.symm
  have hγ𝔔 : (⟨γ, isIntegral_trans _ hγ_int⟩ : 𝓞 L) ∉ 𝔔 := by
    intro hmem
    have hpow : (⟨γ, isIntegral_trans _ hγ_int⟩ : 𝓞 L) ^ p ∈ 𝔔 :=
      Ideal.pow_mem_of_mem 𝔔 hmem _ hpri.out.pos
    have hpoweq : (⟨γ, isIntegral_trans _ hγ_int⟩ : 𝓞 L) ^ p = algebraMap (𝓞 K) (𝓞 L) a := by
      apply NumberField.RingOfIntegers.coe_injective
      simp only [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L]
      exact e
    rw [hpoweq] at hpow
    exact ha_unit (hcomap ▸ Ideal.mem_comap.mpr hpow)
  -- Separability of the shifted polynomial mod `𝔔`, transported down to mod `𝔭`.
  have hsepL := separable_poly_element_mod hp hζ a hcong ha0 γ e hγ_int 𝔔 hγ𝔔
  have hle𝔭 : 𝔭 ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) 𝔔 := le_of_eq hcomap.symm
  letI : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  letI : Field (𝓞 L ⧸ 𝔔) := Ideal.Quotient.field 𝔔
  have hmap : ((polyElement hp hζ a hcong).map (Ideal.Quotient.mk 𝔭)).map
        (Ideal.quotientMap 𝔔 (algebraMap (𝓞 K) (𝓞 L)) hle𝔭)
      = (polyElement hp hζ a hcong).map
          ((Ideal.Quotient.mk 𝔔).comp (algebraMap (𝓞 K) (𝓞 L))) := by
    rw [Polynomial.map_map, Ideal.quotientMap_comp_mk hle𝔭]
  rw [← hmap] at hsepL
  have hsepK : Separable ((polyElement hp hζ a hcong).map (Ideal.Quotient.mk 𝔭)) :=
    (Polynomial.separable_map _).mp hsepL
  -- The shifted root `β` is the generator; its minimal polynomial is `polyElement`.
  have hβint : IsIntegral (𝓞 K)
      ((polyRootElement hp hζ a hcong γ e 0 : 𝓞 L) : L) :=
    IsIntegral.tower_top
      (NumberField.RingOfIntegers.isIntegral_coe (polyRootElement hp hζ a hcong γ e 0))
  have hadjβ : Algebra.adjoin K {((polyRootElement hp hζ a hcong γ e 0 : 𝓞 L) : L)} = ⊤ := by
    have hmem : γ ∈ Algebra.adjoin K {((polyRootElement hp hζ a hcong γ e 0 : 𝓞 L) : L)} :=
      mem_adjoin_polyRoot_element hp hζ a hcong γ e 0
    have hle : Algebra.adjoin K {γ}
        ≤ Algebra.adjoin K {((polyRootElement hp hζ a hcong γ e 0 : 𝓞 L) : L)} :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem)
    rw [hadj] at hle; exact top_le_iff.mp hle
  rw [← minpoly_polyRoot_element' hp hζ a hcong ha_npow γ e 0] at hsepK
  rw [show (𝔭 : Ideal (𝓞 K)) = 𝔔.under (𝓞 K) from h𝔔over.over] at hsepK
  exact isUnramifiedAt_of_Separable_minpoly (R := 𝓞 K) K (S := 𝓞 L) L 𝔔
    (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭bot 𝔔)
    ((polyRootElement hp hζ a hcong γ e 0 : 𝓞 L) : L) hβint hadjβ hsepK

/-! ### Case B helper: `X^p - C u'` is separable mod `I` when `I ≠ 𝔭` and `u'` is an `I`-unit.

This is the **separability ingredient** for the Case B descent (`I ≠ 𝔭` good prime,
generator `γ = d·α` with `γ^p = u'`, minimal polynomial `X^p - C u'`). The separability is
immediate from Mathlib's `Polynomial.separable_X_pow_sub_C` after observing both conditions:
`(p : R/I) ≠ 0` (because `I ≠ 𝔭`, i.e., residue char `≠ p`) and `u' ≠ 0 mod I` (because
`u'` is an `I`-unit). Stated generically for any commutative ring `R` to avoid the heavy
section-variable elaboration on `𝓞 K`; the application at `R = 𝓞 K` is immediate.

Wiring this into the full `IsUnramifiedAt` statement at `I` (via flt-regular's
`isUnramifiedAt_of_Separable_minpoly`) requires constructing the **globally integral**
generator `γ = d·α` and verifying its minimal polynomial really is `X^p - C u'`. That
involves the `IsDedekindDomain.HeightOneSpectrum` prescribed-valuation API and is
substantively bigger than just the separability lemma. -/

section CaseBSeparability

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The core polynomial separability fact (term-mode to avoid heavy tactic-mode whnf):
`X^n - C ((mk I) u')` is separable over the residue field, provided `(n : R/I) ≠ 0` and
`(mk I) u' ≠ 0`. -/
private lemma separable_X_pow_sub_C_modI_core
    (I : Ideal R) [I.IsMaximal] {u' : R}
    (hp_ne : ((n : ℕ) : R ⧸ I) ≠ 0) (hu'_ne : (Ideal.Quotient.mk I) u' ≠ 0) :
    Separable (X ^ n - C ((Ideal.Quotient.mk I) u')) :=
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  Polynomial.separable_X_pow_sub_C _ hp_ne hu'_ne

/-- **Case B separability ingredient.** For any maximal ideal `I` of a commutative ring `R`,
with `(n : R) ∉ I` (equivalently the residue characteristic at `I` is coprime to `n`), and any
`u' : R` that is an `I`-unit (`u' ∉ I`), the polynomial `X^n - C u'` is separable when
reduced modulo `I` over the residue field `R / I`. -/
lemma separable_X_pow_sub_C_modI
    (I : Ideal R) [I.IsMaximal] (hn_unit : (n : R) ∉ I) (u' : R) (hu' : u' ∉ I) :
    Separable ((X ^ n - C u').map (Ideal.Quotient.mk I)) := by
  have hp_ne : ((n : ℕ) : R ⧸ I) ≠ 0 := by
    rw [show ((n : ℕ) : R ⧸ I) = (Ideal.Quotient.mk I) ((n : ℕ) : R) from rfl,
        Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact_mod_cast hn_unit
  have hu'_ne : (Ideal.Quotient.mk I) u' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have eq1 : (X ^ n - C u' : R[X]).map (Ideal.Quotient.mk I)
      = X ^ n - C ((Ideal.Quotient.mk I) u') := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [eq1]
  exact separable_X_pow_sub_C_modI_core I hp_ne hu'_ne

end CaseBSeparability

/-! ### Case A congruence: `π ∣ c - 1 ⟹ π^p ∣ c^p - 1` (the wild-prime multiplier step)

For the wild prime `𝔭 = (π)`, `π = ζ - 1`, the Case-A generator `γ = c·α` is chosen with
`c ≡ 1 mod π`. To feed flt-regular's shifted-polynomial machinery (which needs the congruence
`π^p ∣ a' - 1` where `a' = γ^p`) we upgrade `c ≡ 1 mod π` to `c^p ≡ 1 mod π^p`. This is the
binomial fact: writing `c = 1 + π t`, every term `C(p,k)(π t)^k` (`1 ≤ k ≤ p`) of `c^p - 1` is
divisible by `π^p` — at `k = p` because `(π t)^p = π^p t^p`, and at `1 ≤ k < p` because
`p ∣ C(p,k)` (so `π^{p-1} ∣ C(p,k)` via `associated_zeta_sub_one_pow_prime`) times `π^k`. -/

include hζ in
omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Case A congruence step (two-element form).** If `π = ζ - 1` divides `b - a` in `𝓞 K`,
then `π^p` divides `b^p - a^p`. Binomial expansion: `b = a + π t`, and every `k ≥ 1` term of
`(a + π t)^p - a^p` is `π^p`-divisible (`k = p`: `π^p t^p`; `1 ≤ k < p`: `p ∣ C(p,k)` gives
`π^{p-1} ∣ C(p,k)` via `associated_zeta_sub_one_pow_prime`, times `π^k`). The `a = 1` special
case is `zeta_sub_one_pow_dvd_pow_sub_one`. -/
lemma zeta_sub_one_pow_dvd_pow_sub_pow {a b : 𝓞 K}
    (hab : (hζ.unit' - 1 : 𝓞 K) ∣ b - a) :
    (hζ.unit' - 1 : 𝓞 K) ^ p ∣ b ^ p - a ^ p := by
  set π : 𝓞 K := hζ.unit' - 1 with hπ
  obtain ⟨t, ht⟩ := hab
  have hbval : b = π * t + a := by linear_combination ht
  rw [hbval, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul,
    add_sub_cancel_right]
  refine Finset.dvd_sum (fun k hk => ?_)
  have hklt : k < p := Finset.mem_range.mp hk
  -- Goal: `π^p ∣ (π t)^(k+1) · a^(p-(k+1)) · ↑C(p,k+1)`.
  rw [mul_pow]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hklt) with heq | hlt
  · -- k + 1 = p : the `π^(k+1) = π^p` factor already divides.
    have hpk : π ^ p ∣ π ^ (k + 1) := pow_dvd_pow π heq.ge
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpk _) _) _
  · -- k + 1 < p : `π^(p-1) ∣ ↑C(p,k+1)` (from `p ∣ C(p,k+1)`), times `π^(k+1)`.
    have hpc : p ∣ p.choose (k + 1) :=
      Nat.Prime.dvd_choose_self hpri.out (Nat.succ_ne_zero k) hlt
    have h1 : (p : 𝓞 K) ∣ (↑(p.choose (k + 1)) : 𝓞 K) := by exact_mod_cast Nat.cast_dvd_cast hpc
    have hcast : π ^ (p - 1) ∣ (↑(p.choose (k + 1)) : 𝓞 K) :=
      ((associated_zeta_sub_one_pow_prime hζ).dvd).trans h1
    have hple : p ≤ (k + 1) + (p - 1) := by omega
    have hdvd1 : π ^ p ∣ π ^ (k + 1) * π ^ (p - 1) := by
      rw [← pow_add]; exact pow_dvd_pow π hple
    exact hdvd1.trans
      (mul_dvd_mul (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left dvd_rfl _) _) hcast)

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
include hζ in
/-- **Case A congruence step.** If `π = ζ - 1` divides `c - 1` in `𝓞 K`, then `π^p` divides
`c^p - 1`. The `a = 1` special case of `zeta_sub_one_pow_dvd_pow_sub_pow`. -/
lemma zeta_sub_one_pow_dvd_pow_sub_one {c : 𝓞 K}
    (hc : (hζ.unit' - 1 : 𝓞 K) ∣ c - 1) :
    (hζ.unit' - 1 : 𝓞 K) ^ p ∣ c ^ p - 1 := by
  simpa using zeta_sub_one_pow_dvd_pow_sub_pow hζ (a := 1) (b := c) (by simpa using hc)

/-! ### The linchpin: class-group-free generator existence

For an invertible fractional ideal `Jinv` and a proper ideal `I ⊊ R` (Dedekind domain `R`),
the strict inclusion `Jinv · I ⊊ Jinv` yields an element `d ∈ Jinv` with `d ∉ Jinv · I`. This
is the elementary fractional-ideal fact (no class group, no CRT) that manufactures
the globally-integral per-prime generators for both
cases A and B (`γ = d · α` is globally integral iff `d ∈ J⁻¹`, and `d ∉ J⁻¹·I` pins the exact
`I`-valuation that makes `γ^p` an `I`-unit). See the file header "The linchpin". -/

section Linchpin

open scoped nonZeroDivisors

/-- **Linchpin existence lemma.** In a Dedekind domain `R` with fraction field `K`, for a
nonzero (hence invertible) fractional ideal `Jinv` and a proper ideal `I ⊊ R`, there is an
element `d ∈ Jinv` with `d ∉ Jinv · I`. -/
lemma exists_mem_inv_not_mem_inv_mul
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (Jinv : FractionalIdeal R⁰ K) (hJinv : Jinv ≠ 0)
    (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ d : K, d ∈ Jinv ∧ d ∉ Jinv * (I : FractionalIdeal R⁰ K) := by
  have hI1 : (I : FractionalIdeal R⁰ K) < 1 := by
    refine lt_of_le_of_ne FractionalIdeal.coeIdeal_le_one ?_
    rw [Ne, FractionalIdeal.coeIdeal_eq_one]
    intro h; exact hI (by simpa using h)
  have hle : Jinv * (I : FractionalIdeal R⁰ K) ≤ Jinv := by
    calc Jinv * (I : FractionalIdeal R⁰ K) ≤ Jinv * 1 := by gcongr
      _ = Jinv := mul_one Jinv
  have hne : Jinv * (I : FractionalIdeal R⁰ K) ≠ Jinv := by
    intro h
    have h2 : Jinv * (I : FractionalIdeal R⁰ K) = Jinv * 1 := h.trans (mul_one Jinv).symm
    exact (ne_of_lt hI1) (mul_left_cancel₀ hJinv h2)
  obtain ⟨d, hd, hd'⟩ := SetLike.not_le_iff_exists.mp (lt_of_le_of_ne hle hne).not_ge
  exact ⟨d, hd, hd'⟩

open FractionalIdeal in
/-- **Case-B generator ingredient.** Given `(u) = J^p` (as `spanSingleton u = J^p`) and a
linchpin element `d ∈ J⁻¹ \ J⁻¹·I` (`I` a prime ideal), the element `u' := u·d^p` is an
algebraic integer (`∈ image of R`) that is an `I`-unit (`u' ∉ I`).

`u' ∈ R`: `spanSingleton (u·d^p) = (J·spanSingleton d)^p ≤ 1` (since `J·spanSingleton d ≤ J·J⁻¹
= 1`). `u' ∉ I`: write `B := J·spanSingleton d = coeIdeal B'`; `d ∉ J⁻¹·I` ⟹ `B ≰ coeIdeal I`
(cancel the invertible `J`) ⟹ `B' ≰ I`; and `(u') = B'^p`, so `u' ∈ I ⟹ B'^p ≤ I ⟹ B' ≤ I`
(`IsPrime.pow_le_iff`), contradiction. -/
lemma exists_isInteger_isUnit_of_linchpin
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {p : ℕ} (hp : 0 < p) (J : FractionalIdeal R⁰ K) (hJ : J ≠ 0) (u : K)
    (hu : spanSingleton R⁰ u = J ^ p)
    (I : Ideal R) [hI : I.IsPrime]
    (d : K) (hd : d ∈ (J⁻¹ : FractionalIdeal R⁰ K))
    (hd' : d ∉ (J⁻¹ * (I : FractionalIdeal R⁰ K))) :
    ∃ u' : R, algebraMap R K u' = u * d ^ p ∧ u' ∉ I := by
  set B : FractionalIdeal R⁰ K := J * spanSingleton R⁰ d with hB
  have hspan : spanSingleton R⁰ (u * d ^ p) = B ^ p := by
    rw [hB, ← spanSingleton_mul_spanSingleton, ← spanSingleton_pow, hu, mul_pow]
  have hble : B ≤ (1 : FractionalIdeal R⁰ K) := by
    rw [hB]
    calc J * spanSingleton R⁰ d ≤ J * J⁻¹ := by gcongr; exact spanSingleton_le_iff_mem.mpr hd
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨B', hB'⟩ := le_one_iff_exists_coeIdeal.mp hble
  have hBnotle : ¬ B ≤ (I : FractionalIdeal R⁰ K) := by
    intro hcon
    apply hd'
    have hstep : (J⁻¹ : FractionalIdeal R⁰ K) * B ≤ J⁻¹ * (I : FractionalIdeal R⁰ K) := by gcongr
    rw [hB, ← mul_assoc, inv_mul_cancel₀ hJ, one_mul] at hstep
    exact spanSingleton_le_iff_mem.mp hstep
  rw [← hB'] at hspan hBnotle
  obtain ⟨u', hu'eq⟩ : ∃ u' : R, algebraMap R K u' = u * d ^ p := by
    rw [← mem_one_iff R⁰, ← spanSingleton_le_iff_mem, hspan, ← coeIdeal_pow]
    exact coeIdeal_le_one
  refine ⟨u', hu'eq, ?_⟩
  intro hmem
  apply hBnotle
  rw [coeIdeal_le_coeIdeal]
  have hspan' : (Ideal.span {u'} : Ideal R) = B' ^ p := by
    apply coeIdeal_injective (K := K)
    change (↑(Ideal.span {u'}) : FractionalIdeal R⁰ K) = ↑(B' ^ p)
    rw [coeIdeal_span_singleton, coeIdeal_pow, ← hspan, hu'eq]
  have hle' : (Ideal.span {u'} : Ideal R) ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hmem
  rw [hspan'] at hle'
  exact (Ideal.IsPrime.pow_le_iff (hP := hI) hp.ne').mp hle'

end Linchpin

/-! ### Case B: `IsUnramifiedAt` at a good prime from a `p`-th-root generator

Given a generator `γ` of `L/K` with `γ^p = u'` (`u' : 𝓞 K`), at a maximal `I` where `u'` is
an `I`-unit and the residue characteristic is coprime to `p`, the extension is unramified at
`I`. This bundles the minpoly computation (`minpoly (𝓞 K) γ = X^p - C u'`) with the
separability ingredient `separable_X_pow_sub_C_modI` and flt-regular's
`isUnramifiedAt_of_Separable_minpoly`. It abstracts over `γ`/`u'`; the concrete instantiation
`isUnramifiedAt_caseB` builds them from the linchpin element `d` (`γ = d·α`, with `d` from
`exists_isInteger_isUnit_of_linchpin`). -/

section CaseB

variable {K : Type*} [Field K] [NumberField K]
  {L : Type*} [Field L] [NumberField L] [Algebra K L]

omit [NumberField L] in
/-- **minpoly of a `p`-th-root generator.** If `γ^n = u'` (`u' : 𝓞 K`), `γ` is integral over
`𝓞 K`, and `X^n - C (u' : K)` is irreducible over `K`, then `minpoly (𝓞 K) γ = X^n - C u'`.
(Computes `minpoly K γ` via `minpoly.eq_of_irreducible_of_monic`, then transports to `𝓞 K`
via `minpoly.isIntegrallyClosed_eq_field_fractions'`.) -/
lemma minpoly_eq_X_pow_sub_C_of_pth_root {n : ℕ} (hn : 0 < n) (γ : L) (u' : 𝓞 K)
    (hγ_int : IsIntegral (𝓞 K) γ)
    (e : γ ^ n = algebraMap (𝓞 K) L u')
    (hirr : Irreducible (X ^ n - C (algebraMap (𝓞 K) K u'))) :
    minpoly (𝓞 K) γ = X ^ n - C u' := by
  apply map_injective (algebraMap (𝓞 K) K) (IsFractionRing.injective (𝓞 K) K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hγ_int]
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C _ hn.ne')).symm
  rw [map_sub, map_pow, aeval_X, aeval_C, ← IsScalarTower.algebraMap_apply, ← e, sub_self]

/-- **Case B (unramified at a good prime).** For a maximal ideal `I` of `𝓞 K` with `(n:𝓞 K) ∉ I`
(residue char coprime to `n` — for `n = p` this is exactly `I ≠ 𝔭`) and a generator `γ` of
`L/K` with `γ^n = u'` an `I`-unit and `X^n - C (u':K)` irreducible, the extension `𝓞 L / 𝓞 K`
is unramified at `I`. -/
lemma isUnramifiedAt_of_pth_root {n : ℕ} (hn : 0 < n) (γ : L) (u' : 𝓞 K)
    (I : Ideal (𝓞 K)) [I.IsMaximal] (hIbot : I ≠ ⊥)
    (hγ_int : IsIntegral (𝓞 K) γ)
    (e : γ ^ n = algebraMap (𝓞 K) L u')
    (hirr : Irreducible (X ^ n - C (algebraMap (𝓞 K) K u')))
    (hadj : Algebra.adjoin K {γ} = ⊤)
    (hn_unit : (n : 𝓞 K) ∉ I) (hu' : u' ∉ I) :
    IsUnramifiedAt (𝓞 L) I := by
  have hminpoly : minpoly (𝓞 K) γ = X ^ n - C u' :=
    minpoly_eq_X_pow_sub_C_of_pth_root hn γ u' hγ_int e hirr
  have hsep : Separable ((X ^ n - C u').map (Ideal.Quotient.mk I)) :=
    separable_X_pow_sub_C_modI I hn_unit u' hu'
  apply isUnramifiedAt_of_forall_isUnramifiedAt hIbot
  intro 𝔔 h𝔔prime h𝔔over
  letI := h𝔔prime
  letI : 𝔔.LiesOver I := h𝔔over
  refine isUnramifiedAt_of_Separable_minpoly (R := 𝓞 K) K (S := 𝓞 L) L 𝔔
    (Ideal.ne_bot_of_liesOver_of_ne_bot hIbot 𝔔) γ (IsIntegral.tower_top hγ_int) hadj ?_
  rw [show 𝔔.under (𝓞 K) = I from h𝔔over.over.symm, hminpoly]; exact hsep

open scoped nonZeroDivisors in
open FractionalIdeal in
/-- **Case B (concrete `p`-th-root generator).** Let `α : L` be a `p`-th root of `u : K`
(`α ^ p = algebraMap K L u`) generating `L/K` (`adjoin K {α} = ⊤`), with `u` not a `p`-th power
in `K` and principal-power fractional ideal `(u) = J^p`. Then at every maximal ideal `I` of
`𝓞 K` with `(p : 𝓞 K) ∉ I` (i.e. `I` is not the prime above `p`), the extension `𝓞 L / 𝓞 K`
is unramified.

The generator is `γ := d · α` for a linchpin element `d ∈ J⁻¹ \ J⁻¹·I`
(`exists_mem_inv_not_mem_inv_mul`): then `u' := u · d^p` is an algebraic integer that is an
`I`-unit (`exists_isInteger_isUnit_of_linchpin`), `γ^p = u'` makes `γ` integral *for free*
(root of the monic `X^p - C u'`), and `X^p - C u'` is irreducible because `u' = u·d^p` is not
a `p`-th power. The conclusion is then `isUnramifiedAt_of_pth_root`. -/
lemma isUnramifiedAt_caseB {p : ℕ} [hpri : Fact p.Prime]
    (u : K) (α : L) (e : α ^ p = algebraMap K L u)
    (hu_npow : ∀ v : K, v ^ p ≠ u)
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    (hspan : spanSingleton (𝓞 K)⁰ u = J ^ p)
    (hadjα : Algebra.adjoin K {α} = ⊤)
    (I : Ideal (𝓞 K)) [hImax : I.IsMaximal] (hIbot : I ≠ ⊥) (hpI : (p : 𝓞 K) ∉ I) :
    IsUnramifiedAt (𝓞 L) I := by
  haveI hIprime : I.IsPrime := hImax.isPrime
  have hItop : I ≠ ⊤ := hImax.ne_top
  have hJinv : (J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := inv_ne_zero hJ
  obtain ⟨d, hd, hd'⟩ := exists_mem_inv_not_mem_inv_mul (J⁻¹) hJinv I hItop
  obtain ⟨u', hu'eq, hu'I⟩ :=
    exists_isInteger_isUnit_of_linchpin hpri.out.pos J hJ u hspan I d hd hd'
  have hd0 : d ≠ 0 := fun h => hd' (h ▸ zero_mem _)
  set γ : L := algebraMap K L d * α with hγdef
  have eγ : γ ^ p = algebraMap (𝓞 K) L u' := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L, hu'eq, hγdef, mul_pow, e, ← map_pow, ← map_mul]
    congr 1; ring
  have hγint : IsIntegral (𝓞 K) γ := by
    refine ⟨X ^ p - C u', monic_X_pow_sub_C u' hpri.out.pos.ne', ?_⟩
    rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, eγ, sub_self]
  have hirr : Irreducible (X ^ p - C (algebraMap (𝓞 K) K u')) := by
    rw [hu'eq]
    refine X_pow_sub_C_irreducible_of_prime hpri.out (fun b hb => ?_)
    exact hu_npow (b / d)
      (by rw [div_pow, hb, mul_div_assoc, div_self (pow_ne_zero p hd0), mul_one])
  have hadjγ : Algebra.adjoin K {γ} = ⊤ := by
    have hαmem : α ∈ Algebra.adjoin K {γ} := by
      have hαeq : α = algebraMap K L d⁻¹ * γ := by
        rw [hγdef, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]
      rw [hαeq]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.self_mem_adjoin_singleton K γ)
    have hle : Algebra.adjoin K {α} ≤ Algebra.adjoin K {γ} :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hαmem)
    rw [hadjα] at hle
    exact top_le_iff.mp hle
  exact isUnramifiedAt_of_pth_root hpri.out.pos γ u' I hIbot hγint eγ hirr hadjγ hpI hu'I

end CaseB

/-! ### Case A: concrete `c·α` generator at the wild prime `𝔭`

The dual of `isUnramifiedAt_caseB` for the single wild prime `𝔭 ∋ ζ - 1`. There the generator
`γ = d·α` has minimal polynomial `X^p - C u'` (separable mod good primes); here `γ = c·α` for a
multiplier `c` with `c ≡ 1 mod 𝔭`, so `a' := u·c^p ≡ 1 mod 𝔭^p` and the **shifted** polynomial
`polyElement` is the minimal polynomial (inseparable `X^p - C a'` is avoided). This lemma takes
the multiplier `c` and the resulting integer `a' = u·c^p` together with the congruence
`(ζ-1)^p ∣ a'-1` as hypotheses; manufacturing `c` (class-group-free, via the linchpin applied to
`J` and `𝔭`) is deferred to the aggregation step, exactly as `isUnramifiedAt_caseB` defers
nothing because its `d` comes from `exists_isInteger_isUnit_of_linchpin` inline. -/
include hp in
lemma isUnramifiedAt_caseA
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (u : K) (α : L) (e : α ^ p = algebraMap K L u)
    (hu_npow : ∀ v : K, v ^ p ≠ u)
    (hadjα : Algebra.adjoin K {α} = ⊤)
    (𝔭 : Ideal (𝓞 K)) [h𝔭max : 𝔭.IsMaximal] (hπ𝔭 : (hζ.unit' - 1 : 𝓞 K) ∈ 𝔭)
    (c : K) (hc0 : c ≠ 0) (a' : 𝓞 K) (ha' : algebraMap (𝓞 K) K a' = u * c ^ p)
    (ha'cong : (hζ.unit' - 1 : 𝓞 K) ^ p ∣ a' - 1) :
    IsUnramifiedAt (𝓞 L) 𝔭 := by
  set γ : L := algebraMap K L c * α with hγdef
  have eγ : γ ^ p = algebraMap (𝓞 K) L a' := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L, ha', hγdef, mul_pow, e, ← map_pow, ← map_mul]
    congr 1; ring
  have hγint : IsIntegral (𝓞 K) γ := by
    refine ⟨X ^ p - C a', monic_X_pow_sub_C a' hpri.out.pos.ne', ?_⟩
    rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, eγ, sub_self]
  have ha'_npow : ∀ v : K, v ^ p ≠ algebraMap (𝓞 K) K a' := by
    intro v hv
    rw [ha'] at hv
    exact hu_npow (v / c)
      (by rw [div_pow, hv, mul_div_assoc, div_self (pow_ne_zero p hc0), mul_one])
  have hadjγ : Algebra.adjoin K {γ} = ⊤ := by
    have hαmem : α ∈ Algebra.adjoin K {γ} := by
      have hαeq : α = algebraMap K L c⁻¹ * γ := by
        rw [hγdef, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [hαeq]
      exact mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.self_mem_adjoin_singleton K γ)
    have hle : Algebra.adjoin K {α} ≤ Algebra.adjoin K {γ} :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hαmem)
    rw [hadjα] at hle
    exact top_le_iff.mp hle
  exact isUnramifiedAt_caseA_core hp hζ a' ha'cong ha'_npow γ eγ hγint hadjγ 𝔭 hπ𝔭

/-! ### Aggregation: per-prime Case A / Case B ⟹ global `IsUnramified`

`IsUnramified (𝓞 K) (𝓞 L)` is `∀ p prime, p ≠ ⊥ → IsUnramifiedAt (𝓞 L) p`. For a prime `I`:
* if `(p : 𝓞 K) ∈ I` then `I` lies over `p`, so `(ζ-1) ∈ I` (as `↑p ~ (ζ-1)^{p-1}`) and `I` is
  the unique wild prime `𝔭` — dispatch to `isUnramifiedAt_caseA`;
* otherwise `(p : 𝓞 K) ∉ I` — dispatch to `isUnramifiedAt_caseB`.

The wild-prime multiplier data (`c`, `a' = u·c^p` with `(ζ-1)^p ∣ a'-1`) is taken as the
hypothesis `hwild`; it is the one remaining ingredient, manufactured class-group-free from the
linchpin applied to `J` and `𝔭` together with the descent congruence `u ≡ 1 mod 𝔭^p`. -/
open scoped nonZeroDivisors in
open FractionalIdeal in
include hp in
/-- **(C4) aggregation.** From a `p`-th root `α` of `u` generating `L/K`, with `u` not a `p`-th
power, principal-power ideal `(u) = J^p`, and the wild-prime multiplier data `hwild`, the
extension `𝓞 L / 𝓞 K` is unramified. Dispatches per prime to `isUnramifiedAt_caseA` (wild) or
`isUnramifiedAt_caseB` (good). -/
lemma isUnramified_of_pthRoot
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    (u : K) (α : L) (e : α ^ p = algebraMap K L u)
    (hu_npow : ∀ v : K, v ^ p ≠ u)
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    (hspan : spanSingleton (𝓞 K)⁰ u = J ^ p)
    (hadjα : Algebra.adjoin K {α} = ⊤)
    (hwild : ∃ c : K, c ≠ 0 ∧ ∃ a' : 𝓞 K,
      algebraMap (𝓞 K) K a' = u * c ^ p ∧ (hζ.unit' - 1 : 𝓞 K) ^ p ∣ a' - 1) :
    IsUnramified (𝓞 K) (𝓞 L) := by
  constructor
  intro I hI hIbot
  haveI := hI.isMaximal hIbot
  by_cases hpI : (p : 𝓞 K) ∈ I
  · -- Wild prime: `(ζ-1) ∈ I` via `↑p ~ (ζ-1)^{p-1}`.
    have hπpow : (hζ.unit' - 1 : 𝓞 K) ^ (p - 1) ∈ I := by
      simp only [IsPrimitiveRoot.coe_unit']
      obtain ⟨k, hk⟩ := (associated_zeta_sub_one_pow_prime hζ).symm.dvd
      rw [hk]; exact Ideal.mul_mem_right _ _ hpI
    have hπI : (hζ.unit' - 1 : 𝓞 K) ∈ I := hI.mem_of_pow_mem (p - 1) hπpow
    obtain ⟨c, hc0, a', ha', ha'cong⟩ := hwild
    exact isUnramifiedAt_caseA hp hζ u α e hu_npow hadjα I hπI c hc0 a' ha' ha'cong
  · exact isUnramifiedAt_caseB u α e hu_npow J hJ hspan hadjα I hIbot hpI

/-! ### Wiring to the `AdjoinRoot` shape of the C4 axiom

`isUnramified_of_pthRoot` takes an abstract `p`-th root `α : L`. The C4 axiom's target is the
concrete `L = AdjoinRoot (X^p - C u)`. This lemma instantiates that `L`, taking `α` to be
`AdjoinRoot.root` (`α^p = u`, `adjoin K {α} = ⊤`), and derives `u` is not a `p`-th power from the
`Irreducible (X^p - C u)` instance. The two genuinely descent-derived facts — the principal-power
ideal `(u) = J^p` and the wild-prime multiplier `hwild` — remain as hypotheses; they are exactly
what Washington's Lemma 9.1 establishes from the descent data, and are the only inputs left to
discharge the axiom `isUnramified_routeA_elt`. -/
set_option maxHeartbeats 800000 in -- heavy elaboration: exceeds the default heartbeat budget
open scoped nonZeroDivisors in
open FractionalIdeal in
include hp in
/-- **(C4) wired to `AdjoinRoot`.** For `u : K` with `Irreducible (X^p - C u)`, principal-power
ideal `(u) = J^p`, and wild-prime multiplier data `hwild`, the Kummer extension
`AdjoinRoot (X^p - C u)` is unramified over `𝓞 K`. -/
lemma isUnramified_adjoinRoot_of_pthRoot_data
    (u : K)
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0)
    (hspan : spanSingleton (𝓞 K)⁰ u = J ^ p)
    (hwild : ∃ c : K, c ≠ 0 ∧ ∃ a' : 𝓞 K,
      algebraMap (𝓞 K) K a' = u * c ^ p ∧ (hζ.unit' - 1 : 𝓞 K) ^ p ∣ a' - 1)
    [Fact (Irreducible (X ^ p - C u))] :
    IsUnramified (𝓞 K) (𝓞 (AdjoinRoot (X ^ p - C u))) := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hu_npow : ∀ v : K, v ^ p ≠ u :=
    pow_ne_of_irreducible_X_pow_sub_C (Fact.out (p := Irreducible (X ^ p - C u)))
      dvd_rfl hpri.out.ne_one
  have hfne : (X ^ p - C u) ≠ 0 := (monic_X_pow_sub_C u hpri.out.ne_zero).ne_zero
  letI : Module K (AdjoinRoot (X ^ p - C u)) := Algebra.toModule
  haveI : Module.Finite K (AdjoinRoot (X ^ p - C u)) := (AdjoinRoot.powerBasis hfne).finite
  haveI : NumberField (AdjoinRoot (X ^ p - C u)) :=
    NumberField.of_module_finite K (AdjoinRoot (X ^ p - C u))
  have e : (AdjoinRoot.root (X ^ p - C u)) ^ p
      = algebraMap K (AdjoinRoot (X ^ p - C u)) u := by
    have h0 := AdjoinRoot.eval₂_root (X ^ p - C u)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
    rw [AdjoinRoot.algebraMap_eq]; exact h0
  have hadjα : Algebra.adjoin K {(AdjoinRoot.root (X ^ p - C u))} = ⊤ :=
    AdjoinRoot.adjoinRoot_eq_top
  exact isUnramified_of_pthRoot hp hζ u (AdjoinRoot.root (X ^ p - C u)) e hu_npow J hJ hspan
    hadjα hwild
