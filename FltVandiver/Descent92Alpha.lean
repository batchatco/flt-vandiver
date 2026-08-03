import FltVandiver.Descent92Extraction
import FltVandiver.RouteA
open CyclotomicNT

/-!
# Descent92, file 3 of 9 — the α-units are p-th powers (Washington's step 2, p. 169)

Washington p. 169: for `a ≢ 0 mod p`, the minus element
`α = −ζ^{−a}(ω + ζ^aθ)/(ω + ζ^{−a}θ)` is a `p`-th power in `K`.

**The key observation**: `α = routeAElt (ζ^a) ω θ` — the SAME element RouteA's proven
(C4)/(C5) chain handles, instantiated at the primitive root `ζ^a`.  So this file is an
adapter: massage the situation equation `ω^p + θ^p = η·λ^m·ξ^p` into RouteA's shape
`ε·((1−ζ^a)^{m₁+1}·ξ)^p` (using the `p ∣ 2m` invariant and `(1−ζ^a) ~ (1−ζ)`), and feed
`routeA_elt_isPowerOfP'`.
-/

namespace FltVandiver.Descent92

open scoped NumberField nonZeroDivisors
open NumberField NumberField.IsCMField Polynomial
open CaseIIVandiverRouteA

variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  [NumberField.IsCMField (CyclotomicField p ℚ)]

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **Step 2** (Washington p. 169, Lemmas 9.1 + 9.2 via RouteA): the α-element at index
`a` is a `p`-th power in `K`. -/
theorem step2_alpha_pth_power {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p)
    (hvand : ¬ p ∣ Fintype.card (ClassGroup
      (𝓞 (maximalRealSubfield (CyclotomicField p ℚ)))))
    {a : ℕ} (ha : a.Coprime p) :
    ∃ w : CyclotomicField p ℚ, w ^ p = routeAElt (ζ ^ a) S.ω S.θ := by
  classical
  have hζa : IsPrimitiveRoot (ζ ^ a) p := hζ.pow_of_coprime a ha
  -- the K-level realness of ω, θ
  have hxc : complexConj (CyclotomicField p ℚ) ((S.ω : 𝓞 (CyclotomicField p ℚ))
      : CyclotomicField p ℚ) = ((S.ω : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) := by
    rw [← coe_ringOfIntegersComplexConj]
    exact congrArg _ S.hω_real
  have hyc : complexConj (CyclotomicField p ℚ) ((S.θ : 𝓞 (CyclotomicField p ℚ))
      : CyclotomicField p ℚ) = ((S.θ : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) := by
    rw [← coe_ringOfIntegersComplexConj]
    exact congrArg _ S.hθ_real
  -- nonvanishing of the factors (𝓞-level, from the situation)
  have hfacO : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      S.ω + ζ' * S.θ ≠ 0 := by
    intro ζ' hζ'mem h0
    have h1 : ∏ ζ'' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        (S.ω + ζ'' * S.θ) = 0 :=
      Finset.prod_eq_zero hζ'mem h0
    rw [prod_factorization S hp] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact S.η.ne_zero h3
      · exact pow_ne_zero _ (lambda0_ne_zero hζ hp) h3
    · exact S.hξ0 (pow_eq_zero_iff (by omega : p ≠ 0) |>.mp h2)
  -- ζ^a powers of ζ𝓞 are roots
  have hpowO : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hamem : hζ.toInteger ^ a ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
      hpowO, one_pow]
  have hODtoK : ∀ (w : 𝓞 (CyclotomicField p ℚ)), w ≠ 0 →
      ((w : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) ≠ 0 := by
    intro w hw
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hw
  have ht : ((hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) = ζ :=
    hζ.coe_toInteger
  have hN : ((S.ω : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ)
      + ζ ^ a * ((S.θ : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) ≠ 0 := by
    have h1 := hODtoK _ (hfacO (hζ.toInteger ^ a) hamem)
    push_cast at h1
    simpa [hζ.coe_toInteger] using h1
  -- the inverse root: (ζ^a)⁻¹ = ζ^{a(p−1)}
  have hainv_mem : hζ.toInteger ^ (a * (p - 1))
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul,
      show a * (p - 1) * p = p * (a * (p - 1)) from by ring, pow_mul, hpowO, one_pow]
  have hzainv : (ζ ^ a)⁻¹ = ζ ^ (a * (p - 1)) := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_add, show a * (p - 1) + a = a * p from by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega]
      ring]
    rw [mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hD : ((S.ω : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ)
      + (ζ ^ a)⁻¹ * ((S.θ : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) ≠ 0 := by
    have h1 := hODtoK _ (hfacO (hζ.toInteger ^ (a * (p - 1))) hainv_mem)
    push_cast at h1
    rw [hzainv]
    simpa [hζ.coe_toInteger] using h1
  have hζa0 : (ζ : CyclotomicField p ℚ) ^ a ≠ 0 :=
    pow_ne_zero _ (hζ.ne_zero (by omega))
  -- the p-divisibility data
  obtain ⟨k, hk⟩ := S.hm_dvd
  have hpa : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hpri.out).mp ha.symm
  have hk2 : 2 ≤ k := by
    have h4 : 2 ∣ p - 1 := by
      have hodd := hpri.out.odd_of_ne_two (by omega)
      rw [Nat.odd_iff] at hodd
      omega
    have h5 : p * (p - 1) ≤ 2 * S.m := by
      have h6 : p * (p - 1) / 2 * 2 = p * (p - 1) := by
        rw [Nat.div_mul_cancel (Dvd.dvd.mul_left h4 p)]
      have h7 := S.hm
      omega
    have h8 : p * (p - 1) ≤ p * k := by omega
    have h9 : p - 1 ≤ k := Nat.le_of_mul_le_mul_left h8 (by omega)
    omega
  -- the (1−ζ^a)-association
  have hane : hζ.toInteger ^ a ≠ 1 := by
    intro h1
    exact hpa ((hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd a).mp h1)
  have hassoc_a : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
      (hζ.toInteger ^ a - 1) :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr hamem)
      (Finset.mem_coe.mpr (Polynomial.one_mem_nthRootsFinset hpri.out.pos)) hane
  obtain ⟨u_a, hu_a⟩ := hassoc_a
  -- the RouteA-shaped equation: ω^p + θ^p = ε·((ζᵃ𝓞 − 1)^{(k−1)+1}·ξ)^p
  have hUu : IsUnit ((-hζ.toInteger ^ (p - 1)) ^ S.m
      * (((u_a⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)) ^ (2 * S.m))
      := by
    refine IsUnit.mul (IsUnit.pow _ (IsUnit.neg ?_)) (IsUnit.pow _ (u_a⁻¹).isUnit)
    rw [show (hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) from rfl]
    exact (hζ.unit'.isUnit).pow _
  have he : S.ω ^ p + S.θ ^ p
      = (((S.η * hUu.unit : (𝓞 (CyclotomicField p ℚ))ˣ))
          : 𝓞 (CyclotomicField p ℚ))
        * ((((hζa.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1)
            ^ ((k - 1) + 1) * S.ξ) ^ p := by
    have hka : ((hζa.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = hζ.toInteger ^ a := rfl
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hka, hk1, S.heq]
    rw [Units.val_mul, IsUnit.unit_spec]
    -- λ^m = (−ζ^{p−1})^m·(1−ζ)^{2m} and (ζᵃ−1)^k·-p-th-power-collapse
    have hlam : (lambda0 hζ) ^ S.m
        = (-hζ.toInteger ^ (p - 1)) ^ S.m * (1 - hζ.toInteger) ^ (2 * S.m) := by
      rw [lambda0_eq_unit_mul_sq hζ hp, mul_pow, ← pow_mul, mul_comm 2 S.m]
    rw [hlam]
    -- ((ζᵃ−1)^k·ξ)^p = (ζᵃ−1)^{2m}·ξ^p and (ζᵃ−1)^{2m} = (ζ−1)^{2m}·u_a^{2m}
    have hcollapse : ((hζ.toInteger ^ a - 1) ^ k * S.ξ) ^ p
        = (hζ.toInteger ^ a - 1) ^ (2 * S.m) * S.ξ ^ p := by
      rw [mul_pow, ← pow_mul, mul_comm k p, ← hk]
    rw [hcollapse]
    have hsub : (hζ.toInteger ^ a - 1) ^ (2 * S.m)
        = (1 - hζ.toInteger) ^ (2 * S.m)
          * (((u_a : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
            ^ (2 * S.m) := by
      rw [← mul_pow, show ((1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)))
          * ((u_a : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          = -((hζ.toInteger - 1)
            * ((u_a : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))) from by
        ring, hu_a, Even.neg_pow ⟨S.m, by omega⟩]
    rw [hsub]
    have huu : (((u_a⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
        * ((u_a : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hone : (((u_a⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
          ^ (2 * S.m)
        * ((u_a : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ (2 * S.m)
        = 1 := by
      rw [← mul_pow, huu, one_pow]
    linear_combination (-((((S.η : (𝓞 (CyclotomicField p ℚ))ˣ))
        : 𝓞 (CyclotomicField p ℚ))
      * (-hζ.toInteger ^ (p - 1)) ^ S.m * (1 - hζ.toInteger) ^ (2 * S.m) * S.ξ ^ p))
      * hone
  -- λ-coprimality transfers to the ζ^a-uniformizer
  have htrans : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
      ∣ (hζ.toInteger ^ a - 1) :=
    ⟨-(((u_a : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)), by
      rw [← hu_a]; ring⟩
  have hka : ((hζa.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = hζ.toInteger ^ a := rfl
  have hy' : ¬ ((hζa.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1
      ∣ S.θ := by
    intro hdvd
    rw [hka] at hdvd
    exact S.hlamθ (htrans.trans hdvd)
  have hz' : ¬ ((hζa.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1
      ∣ S.ξ := by
    intro hdvd
    rw [hka] at hdvd
    exact S.hlamξ (htrans.trans hdvd)
  have hgcd : gcd (Ideal.span {S.ω}) (Ideal.span {S.θ}) = 1 :=
    Ideal.isCoprime_iff_gcd.mp S.hωθ
  exact routeA_elt_isPowerOfP' hζa hp hvand hxc hyc hN hD hζa0 he hy' hz' hgcd
    (by omega)

end FltVandiver.Descent92
