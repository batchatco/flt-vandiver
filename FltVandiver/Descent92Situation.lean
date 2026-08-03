import CyclotomicNT.CaseIKummer
import FltRegular.NumberTheory.Cyclotomic.MoreLemmas
import FltVandiver.DescentM1
import CyclotomicNT.RegularPrimes
import CyclotomicNT.KPlusGalois
open CyclotomicNT

/-!
# Descent92, file 1 of 9 — the §9.1 situation record

The Washington §9.1 descent datum (verified against Washington
1997 pp. 167–175): real `ω, θ, ξ` and a real unit `η` with

  `ω^p + θ^p = η · λ^m · ξ^p`,   `λ = (1−ζ)(1−ζ⁻¹)`,   `m ≥ p(p−1)/2`,

pairwise coprimality, and `λ ∤ ω, θ, ξ`-side conditions.  The rational entry point: a
Case II solution `x^p + y^p = z^p` (`p ∣ z`) yields the level `ω = x, θ = y, ξ = z/p^a`.

This file: the `lambda0` element and its associations, the realness vocabulary, and the
`Situation92` structure.
-/

namespace FltVandiver.Descent92

open scoped NumberField
open NumberField NumberField.IsCMField

variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]

/-- Washington's `λ = (1−ζ)(1−ζ⁻¹)` as an element of `𝓞 ℚ(ζ_p)` (using `ζ⁻¹ = ζ^{p−1}`). -/
noncomputable def lambda0 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) :
    𝓞 (CyclotomicField p ℚ) :=
  (1 - hζ.toInteger) * (1 - hζ.toInteger ^ (p - 1))

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `λ` is an associate of `(1−ζ)²`: the cofactor is the unit `−ζ^{p−1}`. -/
theorem lambda0_eq_unit_mul_sq {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) :
    lambda0 hζ = -hζ.toInteger ^ (p - 1) * (1 - hζ.toInteger) ^ 2 := by
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) hζ.toInteger
        = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hsplit : hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 := by
    rw [show hζ.toInteger ^ (p - 1) * hζ.toInteger = hζ.toInteger ^ (p - 1 + 1) from
      (pow_succ _ _).symm, show p - 1 + 1 = p from by omega, hpow]
  rw [lambda0]
  ring_nf
  linear_combination (hζ.toInteger - 1) * hsplit

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `λ^{(p−1)/2}` is an associate of `p` (Washington: `(λ)^{(p−1)/2} = (p)`). -/
theorem lambda0_pow_associated {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) :
    Associated ((lambda0 hζ) ^ ((p - 1) / 2)) ((p : 𝓞 (CyclotomicField p ℚ))) := by
  have hodd := hpri.out.odd_of_ne_two (by omega)
  have heven : 2 * ((p - 1) / 2) = p - 1 := by
    rw [Nat.odd_iff] at hodd
    omega
  have h1 : (lambda0 hζ) ^ ((p - 1) / 2)
      = (-hζ.toInteger ^ (p - 1)) ^ ((p - 1) / 2) * (1 - hζ.toInteger) ^ (p - 1) := by
    rw [lambda0_eq_unit_mul_sq hζ hp, mul_pow, ← pow_mul, heven]
  have hcoe : ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = hζ.toInteger := rfl
  have h2 : (1 - hζ.toInteger) ^ (p - 1)
      = (((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1)
        ^ (p - 1) := by
    rw [hcoe, show (1 - hζ.toInteger) = -(hζ.toInteger - 1) from by ring,
      Even.neg_pow ⟨(p - 1) / 2, by omega⟩]
  rw [h1, h2]
  have hzu : IsUnit ((-hζ.toInteger ^ (p - 1)) ^ ((p - 1) / 2)) := by
    refine IsUnit.pow _ (IsUnit.neg ?_)
    rw [← hcoe]
    exact (hζ.unit'.isUnit).pow _
  exact Associated.trans
    (Associated.symm (associated_unit_mul_right _ _ hzu))
    (associated_zeta_sub_one_pow_prime hζ)

variable [NumberField.IsCMField (CyclotomicField p ℚ)]

/-- **The §9.1 situation** (Washington 1997, p. 168): real `ω, θ, ξ` and a real unit `η`
with `ω^p + θ^p = η·λ^m·ξ^p`, pairwise coprime and prime to `λ`, with the invariant
`m ≥ p(p−1)/2`.  The descent measure is the number of distinct prime factors of `ξ`. -/
structure Situation92 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) where
  /-- The first real base element (entry: `x`). -/
  ω : 𝓞 (CyclotomicField p ℚ)
  /-- The second real base element (entry: `y`). -/
  θ : 𝓞 (CyclotomicField p ℚ)
  /-- The descent core (entry: `z/p^{v_p(z)}`). -/
  ξ : 𝓞 (CyclotomicField p ℚ)
  /-- The real unit. -/
  η : (𝓞 (CyclotomicField p ℚ))ˣ
  /-- The `λ`-exponent. -/
  m : ℕ
  /-- The growth invariant. -/
  hm : p * (p - 1) / 2 ≤ m
  /-- The `p`-divisibility invariant (entry: `2m = ap(p−1)`; preserved by `m ↦ 2m−p`). -/
  hm_dvd : p ∣ 2 * m
  /-- `ω` is real. -/
  hω_real : ringOfIntegersComplexConj (CyclotomicField p ℚ) ω = ω
  /-- `θ` is real. -/
  hθ_real : ringOfIntegersComplexConj (CyclotomicField p ℚ) θ = θ
  /-- `ξ` is real. -/
  hξ_real : ringOfIntegersComplexConj (CyclotomicField p ℚ) ξ = ξ
  /-- `η` is real. -/
  hη_real : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      ((η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
    = ((η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
  /-- The level equation `ω^p + θ^p = η·λ^m·ξ^p`. -/
  heq : ω ^ p + θ ^ p
    = ((η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      * (lambda0 hζ) ^ m * ξ ^ p
  /-- `ω`, `θ` coprime (as ideals). -/
  hωθ : IsCoprime (Ideal.span {ω}) (Ideal.span {θ})
  /-- `ω`, `ξ` coprime (as ideals). -/
  hωξ : IsCoprime (Ideal.span {ω}) (Ideal.span {ξ})
  /-- `θ`, `ξ` coprime (as ideals). -/
  hθξ : IsCoprime (Ideal.span {θ}) (Ideal.span {ξ})
  /-- `ω` is prime to `λ` (equivalently to `1 − ζ`). -/
  hlamω : ¬ (1 - hζ.toInteger) ∣ ω
  /-- `θ` is prime to `λ`. -/
  hlamθ : ¬ (1 - hζ.toInteger) ∣ θ
  /-- `ξ` is prime to `λ`. -/
  hlamξ : ¬ (1 - hζ.toInteger) ∣ ξ
  /-- Nontriviality. -/
  hξ0 : ξ ≠ 0

/-! ### Conjugation vocabulary -/

omit hpri [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] [IsCMField (CyclotomicField p ℚ)] in
/-- Conjugation fixes rational integers. -/
theorem conjO_intCast [NumberField.IsCMField (CyclotomicField p ℚ)] (n : ℤ) :
    ringOfIntegersComplexConj (CyclotomicField p ℚ) ((n : ℤ) : 𝓞 (CyclotomicField p ℚ))
      = ((n : ℤ) : 𝓞 (CyclotomicField p ℚ)) :=
  map_intCast _ n

omit [IsCMField (CyclotomicField p ℚ)] in
omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- Conjugation sends `ζ𝓞` to `ζ𝓞^{p−1}`. -/
theorem conjO_toInteger [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) :
    ringOfIntegersComplexConj (CyclotomicField p ℚ) hζ.toInteger
      = hζ.toInteger ^ (p - 1) := by
  have hp0 : 0 < p := hpri.out.pos
  apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
    (CyclotomicField p ℚ)
  rw [show (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ))
      (ringOfIntegersComplexConj (CyclotomicField p ℚ) hζ.toInteger)
      = complexConj (CyclotomicField p ℚ)
        ((algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)) hζ.toInteger)
    from coe_ringOfIntegersComplexConj _ _]
  have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) hζ.toInteger
      = ζ := hζ.coe_toInteger
  rw [ht, complexConj_zeta hζ, map_pow, ht]
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [show ζ ^ (p - 1) * ζ = ζ ^ p from by
    rw [← pow_succ, show p - 1 + 1 = p from by omega]]
  exact hζ.pow_eq_one

omit [IsCMField (CyclotomicField p ℚ)] in
omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `λ` is real. -/
theorem conjO_lambda0 [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) :
    ringOfIntegersComplexConj (CyclotomicField p ℚ) (lambda0 hζ) = lambda0 hζ := by
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) hζ.toInteger
        = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hsq : (hζ.toInteger ^ (p - 1)) ^ (p - 1) = hζ.toInteger := by
    have h1 : (p - 1) * (p - 1) = p * (p - 2) + 1 := by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega, show 2 ≤ p from h2]
      ring
    rw [← pow_mul, h1, pow_add, pow_mul, hpow, one_pow, pow_one, one_mul]
  simp only [lambda0, map_mul, map_sub, map_one, map_pow, conjO_toInteger hζ]
  rw [hsq]
  ring

/-! ### The rational entry point -/

omit [IsCMField (CyclotomicField p ℚ)] in
omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `π ∣ n` for a rational integer iff `p ∣ n` (Bézout). -/
theorem pi_dvd_intCast_iff {k₀ : Type*} [Field k₀] [NumberField k₀]
    [IsCyclotomicExtension {p} ℚ k₀] {ζ : k₀} (hζ : IsPrimitiveRoot ζ p) {n : ℤ} :
    (hζ.unit'.1 - 1 : 𝓞 k₀) ∣ ((n : ℤ) : 𝓞 k₀) ↔ (p : ℤ) ∣ n := by
  constructor
  · intro h
    exact CyclotomicNT.KummerLog.intCast_mem_zeta_sub_one hζ
      (Ideal.mem_span_singleton.mpr h)
  · intro hpn
    obtain ⟨u, hu⟩ := associated_zeta_sub_one_pow_prime hζ
    have hπp : (hζ.unit'.1 - 1 : 𝓞 k₀) ∣ ((p : ℤ) : 𝓞 k₀) := by
      refine ⟨(hζ.unit'.1 - 1) ^ (p - 2) * u, ?_⟩
      have hsplit : (p : ℕ) - 1 = 1 + (p - 2) := by
        have := hpri.out.two_le
        omega
      push_cast
      rw [← hu, hsplit, pow_add, pow_one]
      simp only [IsPrimitiveRoot.coe_unit']
      ring
    obtain ⟨m, hm⟩ := hpn
    refine hπp.trans ⟨(m : 𝓞 k₀), ?_⟩
    rw [hm]
    push_cast
    ring

omit [IsCMField (CyclotomicField p ℚ)] in
/-- `(1−ζ𝓞) ∣ n ↔ p ∣ n` for rational integers. -/
theorem one_sub_zeta_dvd_intCast_iff {ζ : CyclotomicField p ℚ}
    (hζ : IsPrimitiveRoot ζ p) (n : ℤ) :
    (1 - hζ.toInteger) ∣ ((n : ℤ) : 𝓞 (CyclotomicField p ℚ)) ↔ (p : ℤ) ∣ n := by
  rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
      = -(((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1) from by
    rw [show ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = hζ.toInteger from rfl]
    ring]
  rw [neg_dvd]
  exact pi_dvd_intCast_iff hζ

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] [IsCMField (CyclotomicField p ℚ)] in
/-- `λ ≠ 0`. -/
theorem lambda0_ne_zero {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) : lambda0 hζ ≠ 0 := by
  have halg : ∀ x : 𝓞 (CyclotomicField p ℚ),
      algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) x ≠ 0 → x ≠ 0 := by
    intro x hx h0
    exact hx (h0 ▸ map_zero _)
  have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) hζ.toInteger
      = ζ := hζ.coe_toInteger
  refine mul_ne_zero (halg _ ?_) (halg _ ?_)
  · rw [map_sub, map_one, ht, sub_ne_zero]
    exact fun h => hζ.ne_one hpri.out.one_lt h.symm
  · rw [map_sub, map_one, map_pow, ht, sub_ne_zero]
    intro h
    exact (hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)) h.symm

/-- **The rational entry** (Washington p. 168): a rational Case II solution
`x^p + y^p = z^p`, `p ∣ z`, yields a §9.1 situation with `ω = x`, `θ = y`,
`ξ = z/p^{v_p(z)}`. -/
theorem situation92_of_rational {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) {x y z : ℤ} (hxyz : x ^ p + y ^ p = z ^ p)
    (hz0 : z ≠ 0) (hpz : (p : ℤ) ∣ z) (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y)
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z) :
    Nonempty (Situation92 hζ) := by
  classical
  -- extract the p-part of z
  obtain ⟨a, w, hzw, hpw⟩ : ∃ (a : ℕ) (w : ℤ), z = p ^ a * w ∧ ¬ (p : ℤ) ∣ w := by
    have hfin : FiniteMultiplicity ((p : ℤ)) z :=
      Int.finiteMultiplicity_iff.mpr ⟨by
        rw [Int.natAbs_natCast]
        exact hpri.out.ne_one, hz0⟩
    obtain ⟨m, hm1, hm2⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    exact ⟨_, m, hm1, hm2⟩
  have ha1 : 1 ≤ a := by
    by_contra ha
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero, one_mul] at hzw
    exact hpw (hzw ▸ hpz)
  -- the unit: λ^{(p−1)/2}·uu = p
  obtain ⟨uu, huu⟩ := lambda0_pow_associated hζ hp
  have hkey : (lambda0 hζ) ^ (((p - 1) / 2) * (a * p))
      * ((uu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ (a * p)
      = ((p : 𝓞 (CyclotomicField p ℚ))) ^ (a * p) := by
    rw [pow_mul, ← mul_pow, huu]
  -- the equation
  have hO : ((x : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p
      + ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p
      = ((uu ^ (a * p) : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ (((p - 1) / 2) * (a * p))
        * ((w : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p := by
    have h1 : ((x : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p
        + ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p
        = ((p : 𝓞 (CyclotomicField p ℚ))) ^ (a * p)
          * ((w : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p := by
      have h2 := congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 (CyclotomicField p ℚ))) hxyz
      push_cast at h2
      rw [h2, hzw]
      push_cast
      rw [mul_pow, ← pow_mul]
    rw [h1, ← hkey, Units.val_pow_eq_pow_val]
    ring
  -- η is real (cancel λ^m against the conjugated key equation)
  have hlamne : (lambda0 hζ) ^ (((p - 1) / 2) * (a * p)) ≠ 0 :=
    pow_ne_zero _ (lambda0_ne_zero hζ hp)
  have hηreal : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      (((uu ^ (a * p) : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
      = (((uu ^ (a * p) : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hkey
    simp only [map_mul, map_pow, map_natCast, conjO_lambda0 hζ] at h1
    rw [← hkey] at h1
    have h2 := mul_left_cancel₀ hlamne h1
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact h2
  -- coprimality transfers
  have hcast : ∀ {u v : ℤ}, IsCoprime u v →
      IsCoprime (Ideal.span {((u : ℤ) : 𝓞 (CyclotomicField p ℚ))})
        (Ideal.span {((v : ℤ) : 𝓞 (CyclotomicField p ℚ))}) := by
    intro u v huv
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (huv.map (Int.castRingHom (𝓞 (CyclotomicField p ℚ))))
  have hw_dvd : w ∣ z := ⟨p ^ a, by rw [hzw]; ring⟩
  refine ⟨{
    ω := ((x : ℤ) : 𝓞 (CyclotomicField p ℚ))
    θ := ((y : ℤ) : 𝓞 (CyclotomicField p ℚ))
    ξ := ((w : ℤ) : 𝓞 (CyclotomicField p ℚ))
    η := uu ^ (a * p)
    m := ((p - 1) / 2) * (a * p)
    hm := ?_
    hm_dvd := ?_
    hω_real := conjO_intCast x
    hθ_real := conjO_intCast y
    hξ_real := conjO_intCast w
    hη_real := hηreal
    heq := hO
    hωθ := hcast hxy
    hωξ := hcast (IsCoprime.of_isCoprime_of_dvd_right hxz hw_dvd)
    hθξ := hcast (IsCoprime.of_isCoprime_of_dvd_right hyz hw_dvd)
    hlamω := fun h => hpx ((one_sub_zeta_dvd_intCast_iff hζ x).mp h)
    hlamθ := fun h => hpy ((one_sub_zeta_dvd_intCast_iff hζ y).mp h)
    hlamξ := fun h => hpw ((one_sub_zeta_dvd_intCast_iff hζ w).mp h)
    hξ0 := fun h => by
      have hw0 : w = 0 := by exact_mod_cast h
      exact hz0 (by rw [hzw, hw0, mul_zero]) }⟩
  -- the m-invariant (refine_1 = hm)
  case refine_2 => exact ⟨2 * ((p - 1) / 2) * a, by ring⟩
  have hev : 2 ∣ p - 1 := by
    have hodd := hpri.out.odd_of_ne_two (by omega)
    rw [Nat.odd_iff] at hodd
    omega
  have h1 : p * (p - 1) / 2 = p * ((p - 1) / 2) := Nat.mul_div_assoc p hev
  rw [h1, mul_comm p ((p - 1) / 2)]
  exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left p (by omega))

end FltVandiver.Descent92
