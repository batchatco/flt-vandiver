import FltVandiver.Lemma92Step4
import CyclotomicNT.RegularPrimes
import FltVandiver.Descent
import FltVandiver.UnramifiedRouteA
open CyclotomicNT

/-!
# Washington §9.1 descent — Route A (the minus-element route)

The Case-II descent, restructured around the **minus element**
`u = (-ζ⁻¹)(x+ζy)/(x+ζ⁻¹y)` (Washington §9.1).  All of it is proven, axiom-clean:

* **(C1)** `sigma_routeA_elt` — `σ u = u⁻¹` (`u` is a minus element).
* **(C2)** `routeA_a_principal` — `u = wᵖ ⟹ 𝔞(ζ)` principal (the class-group bridge:
  `routeA_cross_mul`/`heq_of_unit_cross_mul`/… → `B1_principal`).
* **(C4)** `isUnramified_routeA_elt` — element-level Kummer unramifiedness, proven from
  `routeA_elt_ideal_pth_power` + `routeA_elt_wild_multiplier` through the per-prime
  machinery of `UnramifiedRouteA.lean`.
* **(C5)** `routeA_elt_isPowerOfP` / `routeA_elt_isPowerOfP'` — minus element + unramified
  ⟹ `u` is a `p`-th power, via the element-level Lemma 9.2
  `cyclotomic_p_dvd_classNumber`.

The descent recombination (C6) and the top-level Case II live in
`Descent92*.lean` (`caseII_vandiver_route_a`). -/

open NumberField Ideal Polynomial NumberField.IsCMField NumberField.Units
open scoped nonZeroDivisors

namespace CaseIIVandiverRouteA

variable {p : ℕ} [Fact p.Prime]

/-- The descent's minus element `u = (-ζ⁻¹)(x+ζy)/(x+ζ⁻¹y) ∈ K`. -/
noncomputable def routeAElt (ζ : CyclotomicField p ℚ) (x y : 𝓞 (CyclotomicField p ℚ)) :
    CyclotomicField p ℚ :=
  (-ζ⁻¹) * ((x : CyclotomicField p ℚ) + ζ * (y : CyclotomicField p ℚ)) /
    ((x : CyclotomicField p ℚ) + ζ⁻¹ * (y : CyclotomicField p ℚ))

variable [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) {x y : 𝓞 (CyclotomicField p ℚ)}

omit [Fact p.Prime] [IsCMField (CyclotomicField p ℚ)]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `u ≠ 0` from the numerator/denominator being nonzero. -/
lemma routeA_elt_ne_zero
    (hN : (x : CyclotomicField p ℚ) + ζ * (y : CyclotomicField p ℚ) ≠ 0)
    (hD : (x : CyclotomicField p ℚ) + ζ⁻¹ * (y : CyclotomicField p ℚ) ≠ 0)
    (hζ0 : ζ ≠ 0) :
    routeAElt ζ x y ≠ 0 := by
  unfold routeAElt
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hζ0)) hN) hD

/-- **Field-algebra core for `ε₁` real.** Once the numerator/denominator of `routeAElt` are the
generator products `ε(ζ-1)aⁿ` and `ε'(ζ⁻¹-1)bⁿ`, the unit/π factors collapse
(`-ζ⁻¹·(ζ-1)/(ζ⁻¹-1) = 1`), leaving `(-ζ⁻¹)(x+ζy)/(x+ζ⁻¹y) = (ε/ε')(a/b)ⁿ`. -/
lemma elt_eq_unit_ratio {F : Type*} [Field F] {n : ℕ} (ζ x y eps eps' a b : F)
    (hN : x + ζ * y = eps * (ζ - 1) * a ^ n) (hD : x + ζ⁻¹ * y = eps' * (ζ⁻¹ - 1) * b ^ n)
    (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (heps' : eps' ≠ 0) (hb : b ≠ 0) :
    (-ζ⁻¹) * (x + ζ * y) / (x + ζ⁻¹ * y) = eps / eps' * (a / b) ^ n := by
  have hζi1 : ζ⁻¹ - 1 ≠ 0 := sub_ne_zero.mpr (fun h => hζ1 (inv_eq_one.mp h))
  have h1ζ : (1 : F) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ1)
  rw [hN, hD, div_pow]
  field_simp
  ring

include hζ

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `complexConj` inverts the primitive root `ζ` (at the field level). -/
lemma complexConj_zeta : complexConj (CyclotomicField p ℚ) ζ = ζ⁻¹ := by
  have hmem : hζ.unit' ∈ torsion (CyclotomicField p ℚ) :=
    (CommGroup.mem_torsion _).mpr
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, NeZero.pos p, hζ.unit'_pow⟩)
  have h := IsCMField.complexConj_torsion (CyclotomicField p ℚ) ⟨hζ.unit', hmem⟩
  have huval : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) ↑hζ.unit' = ζ := rfl
  simpa [huval] using h

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **(C1)** `σ u = u⁻¹`: `u` is a minus element. Needs `x, y` real (`σ x = x`, `σ y = y`). -/
lemma sigma_routeA_elt
    (hxc : complexConj (CyclotomicField p ℚ) (x : CyclotomicField p ℚ)
      = (x : CyclotomicField p ℚ))
    (hyc : complexConj (CyclotomicField p ℚ) (y : CyclotomicField p ℚ)
      = (y : CyclotomicField p ℚ))
    (hN : (x : CyclotomicField p ℚ) + ζ * (y : CyclotomicField p ℚ) ≠ 0)
    (_hD : (x : CyclotomicField p ℚ) + ζ⁻¹ * (y : CyclotomicField p ℚ) ≠ 0)
    (hζ0 : ζ ≠ 0) :
    complexConj (CyclotomicField p ℚ) (routeAElt ζ x y) = (routeAElt ζ x y)⁻¹ := by
  unfold routeAElt
  simp only [map_mul, map_div₀, map_neg, map_inv₀, map_add, complexConj_zeta hζ, hxc, hyc, inv_inv]
  field_simp

omit [IsCMField (CyclotomicField p ℚ)]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `ζ⁻¹` is the image of the integer `(hζ.unit'⁻¹).1`. -/
lemma algebraMap_unit_inv :
    algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) ((hζ.unit'⁻¹).1) = ζ⁻¹ := by
  have h1 : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) (hζ.unit'.1)
          * algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) ((hζ.unit'⁻¹).1) = 1 := by
    rw [← map_mul, ← Units.val_mul]; simp
  exact (inv_eq_of_mul_eq_one_right h1).symm

omit [IsCMField (CyclotomicField p ℚ)]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **(C2)/(B-i) key step.** `u = (-ζ⁻¹)(x+ζy)/(x+ζ⁻¹y)` is the ratio of the two explicit `𝓞 K`
elements `P = (-(hζ.unit'⁻¹).1)·(x + (hζ.unit'.1)·y)` and `D = x + (hζ.unit'⁻¹).1·y`. -/
lemma routeA_elt_eq :
    routeAElt ζ x y
      = algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          ((-(hζ.unit'⁻¹).1) * (x + (hζ.unit'.1) * y))
        / algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          (x + (hζ.unit'⁻¹).1 * y) := by
  rw [routeAElt]
  congr 1

omit [IsCMField (CyclotomicField p ℚ)]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **(C2)/(B-i) cross-multiplication.** From `u = wᵖ` (`w = a/b` via `IsLocalization.surj`) and
`routeA_elt_eq`, cross-multiply and pull back along the injective `algebraMap` to the `𝓞 K`
identity `P·bᵖ = aᵖ·D` (with `P = (-(hζ.unit'⁻¹).1)·(x+(hζ.unit'.1)·y)`, `D = x+(hζ.unit'⁻¹).1·y`).
This is the hypothesis of `Descent.heq_of_unit_cross_mul` (with `u₀ = -hζ.unit'⁻¹`). -/
lemma routeA_cross_mul
    (hD : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
            (x + (hζ.unit'⁻¹).1 * y) ≠ 0)
    {w : CyclotomicField p ℚ} (hw : w ^ p = routeAElt ζ x y) :
    ∃ a b : 𝓞 (CyclotomicField p ℚ), b ≠ 0 ∧
      ((-(hζ.unit'⁻¹).1) * (x + (hζ.unit'.1) * y)) * b ^ p
        = a ^ p * (x + (hζ.unit'⁻¹).1 * y) := by
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj (𝓞 (CyclotomicField p ℚ))⁰ w
  refine ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp hb, ?_⟩
  have hP : w ^ p * algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
            (x + (hζ.unit'⁻¹).1 * y)
          = algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
            ((-(hζ.unit'⁻¹).1) * (x + (hζ.unit'.1) * y)) := by
    rw [hw, routeA_elt_eq hζ]; exact div_mul_cancel₀ _ hD
  have key : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
              ((-(hζ.unit'⁻¹).1) * (x + (hζ.unit'.1) * y))
            * algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) b ^ p
           = algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) a ^ p
            * algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
              (x + (hζ.unit'⁻¹).1 * y) := by
    rw [← hP, mul_right_comm, ← mul_pow, hab]
  rw [← map_pow, ← map_pow, ← map_mul, ← map_mul] at key
  exact FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) key

/-- `ζ` (as the integer `hζ.unit'.1`) packaged as an element of `nthRootsFinset`. -/
noncomputable def zetaRoot : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) :=
  ⟨hζ.unit'.1, by
    rw [Polynomial.mem_nthRootsFinset (NeZero.pos p), ← Units.val_pow_eq_pow_val, hζ.unit'_pow,
      Units.val_one]⟩

omit [IsCMField (CyclotomicField p ℚ)]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
@[simp] lemma coe_zetaRoot :
    ((zetaRoot hζ : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))) : 𝓞 (CyclotomicField p ℚ))
      = hζ.unit'.1 := rfl

omit [IsCMField (CyclotomicField p ℚ)]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `η⁻¹` of `ζ` is the integer `(hζ.unit'⁻¹).1`. -/
lemma coe_eta_inv_zetaRoot :
    ((CaseIIVandiverDescent.η_inv (zetaRoot hζ)
        : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))) : 𝓞 (CyclotomicField p ℚ))
      = (hζ.unit'⁻¹).1 := by
  change (hζ.unit'.1) ^ (p - 1) = (hζ.unit'⁻¹).1
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  have hmul : hζ.unit' ^ (p - 1) * hζ.unit' = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_lt.le, hζ.unit'_pow]
  exact mul_eq_one_iff_eq_inv.mp hmul

omit [IsCMField (CyclotomicField p ℚ)] in
/-- **(C4 descent fact 1) — the minus element's ideal is a `p`-th power.**
For the descent's minus element `u = routeAElt ζ x y`, the principal fractional ideal `(u)` is a
`p`-th power `J^p`, namely `J = 𝔞(ζ)/𝔞(ζ⁻¹)` with `𝔞(η) := rootDivZetaSubOneDvdGcd …`
(`𝔞(η)^p = 𝔠(η)`). PROVEN from flt-regular's cascade: `(u) = (x+ζy)/(x+ζ⁻¹y)` (the unit `-ζ⁻¹`
drops), and `(x+yη₁)/(x+yη₂) = 𝔠(η₁)/𝔠(η₂)` (`c_div_principal_aux`, the `𝔪`/`𝔭` factors cancel),
with each `𝔠(η) = 𝔞(η)^p`. -/
theorem routeA_elt_ideal_pth_power (hp : p ≠ 2)
    {z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (_hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) (_hm1 : 1 ≤ m) :
    ∃ J : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰ (CyclotomicField p ℚ), J ≠ 0 ∧
      FractionalIdeal.spanSingleton (𝓞 (CyclotomicField p ℚ))⁰ (routeAElt ζ x y) = J ^ p := by
  set K := CyclotomicField p ℚ
  set η : nthRootsFinset p (1 : 𝓞 K) := zetaRoot hζ with hηdef
  set ηi : nthRootsFinset p (1 : 𝓞 K) := CaseIIVandiverDescent.η_inv (zetaRoot hζ) with hηidef
  have hcoeη : (η : 𝓞 K) = hζ.unit'.1 := coe_zetaRoot hζ
  have hcoeηi : (ηi : 𝓞 K) = (hζ.unit'⁻¹).1 := coe_eta_inv_zetaRoot hζ
  have hxyη : x + y * (η : 𝓞 K) ≠ 0 := x_plus_y_mul_ne_zero hp hζ e hz η
  -- `𝔞(η)` is nonzero (its `p`-th power `𝔠(η)` is, since `𝔪·𝔠(η)·𝔭 = (x+yη) ≠ 0`).
  have hA_ne : rootDivZetaSubOneDvdGcd hp hζ e hy η ≠ 0 := by
    intro h0
    have hc := root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy η
    rw [h0, zero_pow (Fact.out : Nat.Prime p).ne_zero] at hc
    have hmm := m_mul_c_mul_p hp hζ e hy η
    rw [← hc, mul_zero, zero_mul] at hmm
    rw [Ideal.zero_eq_bot, eq_comm, Ideal.span_singleton_eq_bot] at hmm
    exact hxyη hmm
  have hAi_ne : rootDivZetaSubOneDvdGcd hp hζ e hy ηi ≠ 0 := by
    intro h0
    have hc := root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy ηi
    rw [h0, zero_pow (Fact.out : Nat.Prime p).ne_zero] at hc
    have hmm := m_mul_c_mul_p hp hζ e hy ηi
    rw [← hc, mul_zero, zero_mul] at hmm
    rw [Ideal.zero_eq_bot, eq_comm, Ideal.span_singleton_eq_bot] at hmm
    exact x_plus_y_mul_ne_zero hp hζ e hz ηi hmm
  -- The span equalities matching the cascade factors with `routeAElt`'s numerator/denominator.
  have hspanP : Ideal.span {x + y * (η : 𝓞 K)}
      = Ideal.span {(-(hζ.unit'⁻¹).1) * (x + (hζ.unit'.1) * y)} := by
    rw [hcoeη, Ideal.span_singleton_mul_left_unit (Units.isUnit hζ.unit'⁻¹).neg,
      mul_comm (hζ.unit'.1) y]
  have hspanD : Ideal.span {x + y * (ηi : 𝓞 K)} = Ideal.span {x + (hζ.unit'⁻¹).1 * y} := by
    rw [hcoeηi, mul_comm y]
  refine ⟨(rootDivZetaSubOneDvdGcd hp hζ e hy η : FractionalIdeal (𝓞 K)⁰ K)
      / (rootDivZetaSubOneDvdGcd hp hζ e hy ηi : FractionalIdeal (𝓞 K)⁰ K),
      div_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hA_ne)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hAi_ne), ?_⟩
  rw [div_pow, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_pow,
    root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy η,
    root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy ηi,
    ← c_div_principal_aux hp hζ e hy η ηi, hspanP, hspanD,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_div_spanSingleton, ← routeA_elt_eq hζ]

open CaseIIVandiverDescent in
/-- **(C4 descent fact 2) — the wild-prime multiplier.**
There is `c ∈ K` and an integer `a' = u·c^p` with `(ζ-1)^p ∣ a' - 1`. PROVEN from Washington's
§9.1 congruence `u ≡ 1 mod 𝔭^p`. The clean elementary witness (no fractional-ideal linchpin):
write `x+ζy = π·w₁`, `x+ζ⁻¹y = π·w₂` (`w₁,w₂ ∈ 𝓞`, `w₂` a `𝔭`-unit), take `t ∈ 𝓞` with
`w₂t ≡ 1 mod π` and `c := w₂t`, `a' := (-ζ⁻¹·w₁·w₂^{p-1})·t^p = u·c^p`. The congruence reduces to
`π^p ∣ a'₀ - w₂^p` (where `a'₀ = u·w₂^p`), and the identity `π(-ζ⁻¹w₁ - w₂) = -(1+ζ⁻¹)(x+y)`
turns it into `π^{p+1} ∣ (x+y)`, which is `pow_dvd_x_plus_y` (`v_𝔭(x+y) = pm+1 ≥ p+1` for `m ≥ 1`,
real `x,y`). -/
theorem routeA_elt_wild_multiplier (hp : p ≠ 2)
    {z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) (hm1 : 1 ≤ m)
    (hxc : complexConj (CyclotomicField p ℚ) (x : CyclotomicField p ℚ)
      = (x : CyclotomicField p ℚ))
    (hyc : complexConj (CyclotomicField p ℚ) (y : CyclotomicField p ℚ)
      = (y : CyclotomicField p ℚ)) :
    ∃ c : CyclotomicField p ℚ, c ≠ 0 ∧ ∃ a' : 𝓞 (CyclotomicField p ℚ),
      algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) a'
          = routeAElt ζ x y * c ^ p ∧
        (hζ.unit' - 1 : 𝓞 (CyclotomicField p ℚ)) ^ p ∣ a' - 1 := by
  have hpri : Nat.Prime p := Fact.out
  have hπ_ne : (hζ.unit'.1 - 1 : 𝓞 (CyclotomicField p ℚ)) ≠ 0 :=
    hζ.unit'_coe.sub_one_ne_zero hpri.one_lt
  have hπ_prime : Prime (hζ.unit'.1 - 1 : 𝓞 (CyclotomicField p ℚ)) := hζ.zeta_sub_one_prime'
  -- ring-level realness
  have hx_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x :=
    NumberField.RingOfIntegers.coe_injective hxc
  have hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y :=
    NumberField.RingOfIntegers.coe_injective hyc
  set η : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := zetaRoot hζ with hηdef
  set ηi : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) :=
    CaseIIVandiverDescent.η_inv (zetaRoot hζ) with hηidef
  have hcoeη : (η : 𝓞 (CyclotomicField p ℚ)) = hζ.unit'.1 := coe_zetaRoot hζ
  have hcoeηi : (ηi : 𝓞 (CyclotomicField p ℚ)) = (hζ.unit'⁻¹).1 := coe_eta_inv_zetaRoot hζ
  obtain ⟨w1, hw1⟩ : (hζ.unit'.1 - 1) ∣ x + y * (η : 𝓞 (CyclotomicField p ℚ)) :=
    one_sub_zeta_dvd_zeta_pow_sub hp hζ e η
  obtain ⟨w2, hw2⟩ : (hζ.unit'.1 - 1) ∣ x + y * (ηi : 𝓞 (CyclotomicField p ℚ)) :=
    one_sub_zeta_dvd_zeta_pow_sub hp hζ e ηi
  -- `N = π·w₁`, `D = π·w₂` (commuted into the `routeAElt` numerator/denominator form)
  have hN : x + hζ.unit'.1 * y = (hζ.unit'.1 - 1) * w1 := by
    rw [mul_comm hζ.unit'.1 y, ← hcoeη]; exact hw1
  have hD' : x + (hζ.unit'⁻¹).1 * y = (hζ.unit'.1 - 1) * w2 := by
    rw [mul_comm (hζ.unit'⁻¹).1 y, ← hcoeηi]; exact hw2
  have hinv : hζ.unit'.1 * (hζ.unit'⁻¹).1 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  -- `η₀ = 1` (real), hence `ηi ≠ η₀`, hence `π ∤ w₂`.
  have hη0 : (zetaSubOneDvdRoot hp hζ e hy : 𝓞 (CyclotomicField p ℚ)) = 1 :=
    eta_zero_eq_one hp hζ e hy hx_real hy_real
  have hζinv_ne_one : (hζ.unit'⁻¹).1 ≠ (1 : 𝓞 (CyclotomicField p ℚ)) := by
    intro h; apply hζ.unit'_coe.ne_one hpri.one_lt; rwa [h, mul_one] at hinv
  have hηi_ne : ηi ≠ zetaSubOneDvdRoot hp hζ e hy := by
    intro h; exact hζinv_ne_one (by rw [← hcoeηi, h, hη0])
  have hπw2 : ¬ (hζ.unit'.1 - 1) ∣ w2 := by
    intro hdvd
    have hcw2 : divZetaSubOneDvdGcd hp hζ e hy ηi = Ideal.span {w2} := by
      have hmm := m_mul_c_mul_p hp hζ e hy ηi
      rw [hm, one_mul, hw2, ← Ideal.span_singleton_mul_span_singleton,
        mul_comm (Ideal.span {hζ.unit'.1 - 1}) (Ideal.span {w2})] at hmm
      exact mul_right_cancel₀ (b := Ideal.span {hζ.unit'.1 - 1})
        (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hπ_ne) hmm
    apply hηi_ne
    rw [← p_dvd_c_iff hp hζ e hy ηi]
    change Ideal.span {hζ.unit'.1 - 1} ∣ divZetaSubOneDvdGcd hp hζ e hy ηi
    rw [hcw2]
    exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hdvd)
  -- `π^{p+1} ∣ (x+y)`
  have hxy : (hζ.unit'.1 - 1) ^ (p * m + 1) ∣ (x + y) :=
    pow_dvd_x_plus_y hp hζ e hy hx_real hy_real hm
  have hple : p + 1 ≤ p * m + 1 := by
    have : p ≤ p * m := Nat.le_mul_of_pos_right p (by omega)
    omega
  have hxyp1 : (hζ.unit'.1 - 1) ^ (p + 1) ∣ (x + y) := (pow_dvd_pow _ hple).trans hxy
  -- `t` with `w₂·t ≡ 1 mod π` via the residue field `𝓞/𝔭`
  haveI hprime_id : (Ideal.span {hζ.unit'.1 - 1} : Ideal (𝓞 (CyclotomicField p ℚ))).IsPrime :=
    (Ideal.span_singleton_prime hπ_ne).mpr hπ_prime
  haveI hmax_id : (Ideal.span {hζ.unit'.1 - 1} : Ideal (𝓞 (CyclotomicField p ℚ))).IsMaximal :=
    hprime_id.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hπ_ne)
  letI : Field ((𝓞 (CyclotomicField p ℚ)) ⧸ Ideal.span {hζ.unit'.1 - 1}) :=
    Ideal.Quotient.field _
  have hw2_ne : Ideal.Quotient.mk (Ideal.span {hζ.unit'.1 - 1}) w2 ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]; exact hπw2
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (Ideal.span {hζ.unit'.1 - 1}) w2)⁻¹
  have hc1 : (hζ.unit'.1 - 1) ∣ w2 * t - 1 := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one,
      ht, mul_inv_cancel₀ hw2_ne, sub_self]
  -- `a'₀ := -ζ⁻¹·w₁·w₂^{p-1}`, and `π^p ∣ a'₀ - w₂^p`
  set a0 : 𝓞 (CyclotomicField p ℚ) := -(hζ.unit'⁻¹).1 * w1 * w2 ^ (p - 1) with ha0
  have hw2p : w2 ^ p = w2 ^ (p - 1) * w2 := by rw [← pow_succ, Nat.sub_add_cancel hpri.one_le]
  have hident : (hζ.unit'.1 - 1) * (-(hζ.unit'⁻¹).1 * w1 - w2)
      = -(1 + (hζ.unit'⁻¹).1) * (x + y) := by
    linear_combination (hζ.unit'⁻¹).1 * hN + hD' - y * hinv
  have hkey : (hζ.unit'.1 - 1) ^ p ∣ a0 - w2 ^ p := by
    have hd : (hζ.unit'.1 - 1) ^ (p + 1)
        ∣ (hζ.unit'.1 - 1) * (-(hζ.unit'⁻¹).1 * w1 - w2) := by
      rw [hident]; exact hxyp1.mul_left _
    rw [pow_succ, mul_comm] at hd
    have hd2 : (hζ.unit'.1 - 1) ^ p ∣ (-(hζ.unit'⁻¹).1 * w1 - w2) :=
      (mul_dvd_mul_iff_left hπ_ne).mp hd
    rw [ha0, hw2p]
    have : -(hζ.unit'⁻¹).1 * w1 * w2 ^ (p - 1) - w2 ^ (p - 1) * w2
        = w2 ^ (p - 1) * (-(hζ.unit'⁻¹).1 * w1 - w2) := by ring
    rw [this]; exact hd2.mul_left _
  -- `D ≠ 0`, `w₂ ≠ 0`, `c := w₂·t ≠ 0`
  have hDne0 : x + (hζ.unit'⁻¹).1 * y ≠ 0 := by
    rw [mul_comm (hζ.unit'⁻¹).1 y, ← hcoeηi]; exact x_plus_y_mul_ne_zero hp hζ e hz ηi
  have hw2ne : w2 ≠ 0 := by
    intro h; rw [h, mul_zero] at hD'; exact hDne0 hD'
  have hcintne : w2 * t ≠ 0 := by
    intro h
    have : (hζ.unit'.1 - 1) ∣ (1 : 𝓞 (CyclotomicField p ℚ)) := by
      have := hc1; rwa [h, zero_sub, dvd_neg] at this
    exact hπ_prime.not_unit (isUnit_of_dvd_one this)
  have hDalg : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
      (x + (hζ.unit'⁻¹).1 * y) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hDne0
  refine ⟨algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) (w2 * t), ?_,
    a0 * t ^ p, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hcintne
  · -- `algebraMap a' = u · c^p`
    rw [routeA_elt_eq hζ, div_mul_eq_mul_div, eq_div_iff hDalg, ← map_pow, ← map_mul, ← map_mul]
    congr 1
    rw [ha0, hN, hD', mul_pow, hw2p]; ring
  · -- `π^p ∣ a' - 1`
    have hcp : (hζ.unit'.1 - 1) ^ p ∣ (w2 * t) ^ p - 1 :=
      zeta_sub_one_pow_dvd_pow_sub_one hζ hc1
    have hsplit : a0 * t ^ p - 1 = t ^ p * (a0 - w2 ^ p) + ((w2 * t) ^ p - 1) := by
      rw [mul_pow]; ring
    rw [hsplit]
    exact dvd_add (hkey.mul_left _) hcp

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **(C4) — element-level Kummer unramifiedness, the descent instance.**
For the descent's minus element `u = routeAElt ζ x y`, the Kummer extension `K(u^{1/p})` is
unramified over `𝓞 K`, **proven** from the two
descent facts above (`routeA_elt_ideal_pth_power`, `routeA_elt_wild_multiplier`) via the per-prime
Kummer-unramifiedness machinery `isUnramified_adjoinRoot_of_pthRoot_data` in
`FltVandiver.UnramifiedRouteA`. The ramification theory — flt-regular's `KummersLemma.isUnramified`
ported from an *integral* generator to the genuinely *fractional* `u`, via a per-prime argument
(shifted polynomial at `𝔭` + residue-field separability at good primes) — is supplied there;
the proof rests on the two number-theoretic §9.1 inputs above. -/
theorem isUnramified_routeA_elt (hp : p ≠ 2)
    {z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) (hm1 : 1 ≤ m)
    (hxc : complexConj (CyclotomicField p ℚ) (x : CyclotomicField p ℚ)
      = (x : CyclotomicField p ℚ))
    (hyc : complexConj (CyclotomicField p ℚ) (y : CyclotomicField p ℚ)
      = (y : CyclotomicField p ℚ))
    [Fact (Irreducible (X ^ p - C (routeAElt ζ x y)))] :
    IsUnramified (𝓞 (CyclotomicField p ℚ))
      (𝓞 (AdjoinRoot (X ^ p - C (routeAElt ζ x y)))) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨J, hJ, hspan⟩ := routeA_elt_ideal_pth_power hζ hp e hy hz hm hm1
  exact isUnramified_adjoinRoot_of_pthRoot_data hp hζ (routeAElt ζ x y) J hJ hspan
    (routeA_elt_wild_multiplier hζ hp e hy hz hm hm1 hxc hyc)

set_option maxHeartbeats 800000 in -- one application of `cyclotomic_p_dvd_classNumber`
omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **(C5)** Given the minus element `u` (`σ u = u⁻¹`) with its Kummer extension unramified, `u` is
a `p`-th power in `K` — under Vandiver `p ∤ h⁺`. Contrapositive of the *element-level* Lemma 9.2
`cyclotomic_p_dvd_classNumber`; no new class-field theory. The unramifiedness is taken as an
instance-guarded hypothesis (it can only be stated once `X^p - C u` is irreducible, i.e. `u` not a
`p`-th power); the (C4) lemma that produces it is the remaining piece. -/
theorem routeA_elt_isPowerOfP (hp : 2 < p)
    (hvand : ¬ p ∣ Fintype.card (ClassGroup (𝓞 (maximalRealSubfield (CyclotomicField p ℚ)))))
    (hxc : complexConj (CyclotomicField p ℚ) (x : CyclotomicField p ℚ)
      = (x : CyclotomicField p ℚ))
    (hyc : complexConj (CyclotomicField p ℚ) (y : CyclotomicField p ℚ)
      = (y : CyclotomicField p ℚ))
    (hN : (x : CyclotomicField p ℚ) + ζ * (y : CyclotomicField p ℚ) ≠ 0)
    (hD : (x : CyclotomicField p ℚ) + ζ⁻¹ * (y : CyclotomicField p ℚ) ≠ 0)
    (hζ0 : ζ ≠ 0)
    (hunram : [Fact (Irreducible (X ^ p - C (routeAElt ζ x y)))] →
      IsUnramified (𝓞 (CyclotomicField p ℚ))
        (𝓞 (AdjoinRoot (X ^ p - C (routeAElt ζ x y))))) :
    ∃ w : CyclotomicField p ℚ, w ^ p = routeAElt ζ x y := by
  by_contra hcon
  push Not at hcon
  haveI hfact : Fact (Irreducible (X ^ p - C (routeAElt ζ x y))) :=
    ⟨X_pow_sub_C_irreducible_of_prime Fact.out hcon⟩
  exact hvand (cyclotomic_p_dvd_classNumber hp
    (routeA_elt_ne_zero hN hD hζ0)
    (sigma_routeA_elt hζ hxc hyc hN hD hζ0)
    hunram)

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **(C5) from the descent data**, with the unramifiedness discharged by the (C4) axiom
`isUnramified_routeA_elt`: under `p ∤ h⁺`, real `x, y`, `𝔪 = (1)`, `m ≥ 1`, the descent's minus
element `u = routeAElt ζ x y` is a `p`-th power in `K`. -/
theorem routeA_elt_isPowerOfP' (hp : 2 < p)
    (hvand : ¬ p ∣ Fintype.card (ClassGroup (𝓞 (maximalRealSubfield (CyclotomicField p ℚ)))))
    (hxc : complexConj (CyclotomicField p ℚ) (x : CyclotomicField p ℚ)
      = (x : CyclotomicField p ℚ))
    (hyc : complexConj (CyclotomicField p ℚ) (y : CyclotomicField p ℚ)
      = (y : CyclotomicField p ℚ))
    (hN : (x : CyclotomicField p ℚ) + ζ * (y : CyclotomicField p ℚ) ≠ 0)
    (hD : (x : CyclotomicField p ℚ) + ζ⁻¹ * (y : CyclotomicField p ℚ) ≠ 0)
    (hζ0 : ζ ≠ 0)
    {z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) (hm1 : 1 ≤ m) :
    ∃ w : CyclotomicField p ℚ, w ^ p = routeAElt ζ x y := by
  refine routeA_elt_isPowerOfP hζ hp hvand hxc hyc hN hD hζ0 ?_
  intro _
  exact isUnramified_routeA_elt hζ (by omega) e hy hz hm hm1 hxc hyc

open CaseIIVandiverDescent in
/-- **(C2) complete → 𝔞(ζ) principal.** Given the descent data, real `x, y`, `𝔪 = (1)`, and a
`p`-th power `u = wᵖ` (the output of (C5)), the cascade ideal `𝔞(ζ)` is principal (`bClass = 1`).
Chains: `routeA_cross_mul` (`u=wᵖ` ⟹ 𝓞K element id) → `heq_of_unit_cross_mul` → `quotient_…` (⟹
`h_quot`) → `B1_principal`. -/
theorem routeA_a_principal (hp : p ≠ 2) (hvand : IsVandiverPrime p)
    {z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (hx_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x)
    (hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1)
    (hN0 : x + hζ.unit'.1 * y ≠ 0) (hD0 : x + (hζ.unit'⁻¹).1 * y ≠ 0)
    {w : CyclotomicField p ℚ} (hw : w ^ p = routeAElt ζ x y)
    (hη : zetaRoot hζ ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη' : η_inv (zetaRoot hζ) ≠ zetaSubOneDvdRoot hp hζ e hy) :
    bClass hp hζ e hy hz (zetaRoot hζ) = 1 := by
  have hDalg : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
      (x + (hζ.unit'⁻¹).1 * y) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hD0
  obtain ⟨a, b, hb, hid⟩ := routeA_cross_mul hζ hDalg hw
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out : Nat.Prime p).ne_zero, zero_mul] at hid
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero _)) hN0)
      (pow_ne_zero _ hb) hid
  have hid' : ((-hζ.unit'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (x + y * ((zetaRoot hζ) : 𝓞 (CyclotomicField p ℚ))) * b ^ p
      = a ^ p * (x + y * ((η_inv (zetaRoot hζ)) : 𝓞 (CyclotomicField p ℚ))) := by
    rw [coe_zetaRoot, coe_eta_inv_zetaRoot, Units.val_neg, mul_comm y hζ.unit'.1,
      mul_comm y ((hζ.unit'⁻¹).1)]
    exact hid
  have heq := heq_of_unit_cross_mul (zetaRoot hζ) hid'
  have hquot := quotient_principal_of_cross_mul hp hζ e hy hz (zetaRoot hζ)
    hx_real hy_real hm ha hb heq
  exact B1_principal hp hvand hζ e hy hz (zetaRoot hζ) hx_real hy_real hm hη hη' hquot

end CaseIIVandiverRouteA
