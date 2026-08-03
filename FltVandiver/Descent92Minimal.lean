import FltVandiver.Descent92Iterate
import FltVandiver.Descent
import FltRegular.NumberTheory.Cyclotomic.CyclRat
open CyclotomicNT

/-!
# Descent92, file 7 of 9 — the minimal case

When the `a = 1` and `a = p−1` factor ideals are trivial (`(ω+ζθ) = (ω+ζ^{p−1}θ) = 𝔭`),
the element `α = −ζ^{p−1}(ω+ζθ)/(ω+ζ^{p−1}θ)` is an anti-real **unit** which is a `p`-th
power (step 2); Frobenius pins `α ≡ ±1 mod π^{p−1}`, the `−1` branch dies on a valuation
count, and the `+1` branch forces `α` to be a root of unity equal to `1` (Kronecker), so
`ω + θ = 0` — contradiction.
-/

namespace FltVandiver.Descent92

open scoped NumberField nonZeroDivisors
open NumberField NumberField.IsCMField Polynomial CaseIIVandiverRouteA

variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  [NumberField.IsCMField (CyclotomicField p ℚ)]

set_option maxHeartbeats 2000000 in -- heavy elaboration: exceeds the default heartbeat budget
/-- **The minimal-case contradiction** (Washington p. 173). -/
theorem minimal_case_contradiction {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 3 < p)
    (hvand' : ¬ p ∣ Fintype.card (ClassGroup
      (𝓞 (maximalRealSubfield (CyclotomicField p ℚ)))))
    (hNE : S.ω + S.θ ≠ 0)
    (hN : Ideal.span {S.ω + hζ.toInteger ^ 1 * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))})
    (hD : Ideal.span {S.ω + hζ.toInteger ^ (p - 1) * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) :
    False := by
  classical
  have hp2 : 2 < p := by omega
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  -- π ∤ 2
  have hπ2 : ¬ (1 - hζ.toInteger) ∣ (2 : 𝓞 (CyclotomicField p ℚ)) := by
    intro h
    have h1 : (1 - hζ.toInteger) ∣ (((2 : ℤ) : 𝓞 (CyclotomicField p ℚ))) := by
      exact_mod_cast h
    have h2 := (one_sub_zeta_dvd_intCast_iff hζ 2).mp h1
    exact absurd (Int.le_of_dvd (by norm_num) h2) (by omega)
  -- the unit decompositions N = π·u₁, D = π·u₂
  obtain ⟨u₁, hu₁⟩ : Associated (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
      (S.ω + hζ.toInteger ^ 1 * S.θ) :=
    (Ideal.span_singleton_eq_span_singleton.mp hN).symm
  obtain ⟨u₂, hu₂⟩ : Associated (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
      (S.ω + hζ.toInteger ^ (p - 1) * S.θ) :=
    (Ideal.span_singleton_eq_span_singleton.mp hD).symm
  -- the α-unit: α := −ζ^{p−1}·u₁·u₂⁻¹
  set αu : (𝓞 (CyclotomicField p ℚ))ˣ := -(hζ.unit' ^ (p - 1)) * u₁ * u₂⁻¹ with hαu
  have hαval : ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = -hζ.toInteger ^ (p - 1)
        * ((u₁ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((u₂⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
    rw [hαu]
    simp only [Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val]
    rfl
  -- the defining relation: αu·D = −ζ^{p−1}·N
  have hαD : ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      * (S.ω + hζ.toInteger ^ (p - 1) * S.θ)
      = -hζ.toInteger ^ (p - 1) * (S.ω + hζ.toInteger ^ 1 * S.θ) := by
    rw [hαval, ← hu₁, ← hu₂]
    have h2 : ((u₂⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((u₂ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    linear_combination (-hζ.toInteger ^ (p - 1) * (1 - hζ.toInteger)
      * ((u₁ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))) * h2
  -- anti-reality: αu·conj(αu) = 1
  have hconjN : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      (S.ω + hζ.toInteger ^ 1 * S.θ) = S.ω + hζ.toInteger ^ (p - 1) * S.θ := by
    rw [map_add, map_mul, map_pow, conjO_toInteger hζ, S.hω_real, S.hθ_real,
      ← pow_mul, mul_one]
  have hconjD : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      (S.ω + hζ.toInteger ^ (p - 1) * S.θ) = S.ω + hζ.toInteger ^ 1 * S.θ := by
    rw [map_add, map_mul, map_pow, conjO_toInteger hζ, S.hω_real, S.hθ_real,
      ← pow_mul]
    congr 2
    refine toInteger_pow_eq_of_mod hζ ?_
    have h1 : (p - 1) * (p - 1) = (p - 2) * p + 1 := by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega, show 2 ≤ p from h2]
      ring
    rw [h1, Nat.mul_add_mod_self_right]
  have hNne : (S.ω + hζ.toInteger ^ 1 * S.θ) ≠ 0 := by
    intro h0
    rw [h0] at hu₁
    exact hπprime.ne_zero (by
      have h4 : (1 - hζ.toInteger) * ((u₁ : (𝓞 (CyclotomicField p ℚ))ˣ)
          : 𝓞 (CyclotomicField p ℚ)) = 0 := hu₁
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact h5
      · exact absurd h5 (Units.ne_zero u₁))
  have hDne : (S.ω + hζ.toInteger ^ (p - 1) * S.θ) ≠ 0 := by
    intro h0
    rw [h0] at hu₂
    exact hπprime.ne_zero (by
      have h4 : (1 - hζ.toInteger) * ((u₂ : (𝓞 (CyclotomicField p ℚ))ˣ)
          : 𝓞 (CyclotomicField p ℚ)) = 0 := hu₂
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact h5
      · exact absurd h5 (Units.ne_zero u₂))
  have hαconj : ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      * ringOfIntegersComplexConj (CyclotomicField p ℚ)
          ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1 := by
    -- conj the defining relation and multiply
    have h1 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hαD
    rw [map_mul, hconjD, map_mul, map_neg, map_pow, conjO_toInteger hζ,
      ← pow_mul, hconjN] at h1
    -- h1 : conj(α)·N = −ζ^{(p−1)²}·D
    have hexp : hζ.toInteger ^ ((p - 1) * (p - 1)) = hζ.toInteger ^ 1 := by
      refine toInteger_pow_eq_of_mod hζ ?_
      have h2 : (p - 1) * (p - 1) = (p - 2) * p + 1 := by
        have h3 := hpri.out.two_le
        zify [show 1 ≤ p from by omega, show 2 ≤ p from h3]
        ring
      rw [h2, Nat.mul_add_mod_self_right]
    rw [hexp, pow_one] at h1
    rw [show (S.ω + hζ.toInteger * S.θ : 𝓞 (CyclotomicField p ℚ))
        = (S.ω + hζ.toInteger ^ 1 * S.θ) from by rw [pow_one]] at h1
    -- multiply hαD and h1; cancel N·D
    have hzeta1 : hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 := by
      rw [← pow_succ, show p - 1 + 1 = p from by omega, hpow]
    have h6 : (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ringOfIntegersComplexConj (CyclotomicField p ℚ)
            ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
        * ((S.ω + hζ.toInteger ^ (p - 1) * S.θ) * (S.ω + hζ.toInteger ^ 1 * S.θ))
        = 1 * ((S.ω + hζ.toInteger ^ (p - 1) * S.θ)
            * (S.ω + hζ.toInteger ^ 1 * S.θ)) := by
      have h7 : ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * (S.ω + hζ.toInteger ^ (p - 1) * S.θ)
          * (ringOfIntegersComplexConj (CyclotomicField p ℚ)
              ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * (S.ω + hζ.toInteger ^ 1 * S.θ))
          = (-hζ.toInteger ^ (p - 1) * (S.ω + hζ.toInteger ^ 1 * S.θ))
            * (-hζ.toInteger * (S.ω + hζ.toInteger ^ (p - 1) * S.θ)) := by
        rw [hαD, h1]
      calc (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * ringOfIntegersComplexConj (CyclotomicField p ℚ)
              ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
          * ((S.ω + hζ.toInteger ^ (p - 1) * S.θ) * (S.ω + hζ.toInteger ^ 1 * S.θ))
          = ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * (S.ω + hζ.toInteger ^ (p - 1) * S.θ)
            * (ringOfIntegersComplexConj (CyclotomicField p ℚ)
                ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * (S.ω + hζ.toInteger ^ 1 * S.θ)) := by ring
        _ = (-hζ.toInteger ^ (p - 1) * (S.ω + hζ.toInteger ^ 1 * S.θ))
            * (-hζ.toInteger * (S.ω + hζ.toInteger ^ (p - 1) * S.θ)) := h7
        _ = 1 * ((S.ω + hζ.toInteger ^ (p - 1) * S.θ)
            * (S.ω + hζ.toInteger ^ 1 * S.θ)) := by
            linear_combination ((S.ω + hζ.toInteger ^ 1 * S.θ)
              * (S.ω + hζ.toInteger ^ (p - 1) * S.θ)) * hzeta1
    exact mul_right_cancel₀ (mul_ne_zero hDne hNne) h6
  -- step 2: α is a p-th power in K
  obtain ⟨w, hw⟩ := step2_alpha_pth_power S hp2 hvand' (a := 1) (Nat.coprime_one_left p)
  -- identify routeAElt with the image of αu
  set f : 𝓞 (CyclotomicField p ℚ) →+* CyclotomicField p ℚ :=
    algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) with hf
  have hfinj : Function.Injective f :=
    FaithfulSMul.algebraMap_injective _ _
  have hζcoe : f hζ.toInteger = ζ := hζ.coe_toInteger
  have hDKne : f (S.ω + hζ.toInteger ^ (p - 1) * S.θ) ≠ 0 := by
    intro h0
    exact hDne (hfinj (by rw [h0, map_zero]))
  have hζK : (ζ : CyclotomicField p ℚ) ^ (p - 1) = ζ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show p - 1 + 1 = p from by omega]
    exact hζ.pow_eq_one
  have hαK : f ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = routeAElt (ζ ^ 1) S.ω S.θ := by
    have h1 := congrArg f hαD
    rw [map_mul, map_mul, map_neg, map_pow, hζcoe] at h1
    -- h1 : f(αu)·f(D) = −ζ^{p−1}·f(N)
    simp only [routeAElt]
    rw [pow_one]
    have hden : ((S.ω : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ)
        + ζ⁻¹ * ((S.θ : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ)
        = f (S.ω + hζ.toInteger ^ (p - 1) * S.θ) := by
      rw [map_add, map_mul, map_pow, hζcoe, hζK]
    have hnum : ((S.ω : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ)
        + ζ * ((S.θ : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ)
        = f (S.ω + hζ.toInteger ^ 1 * S.θ) := by
      rw [map_add, map_mul, map_pow, hζcoe, pow_one]
    rw [hden, hnum, eq_div_iff hDKne, h1, hζK]
  -- w is an integral unit with w^p = α
  have hwint : IsIntegral ℤ w := by
    refine IsIntegral.of_pow (n := p) hpri.out.pos ?_
    rw [hw, ← hαK]
    exact RingOfIntegers.isIntegral_coe _
  set w𝓞 : 𝓞 (CyclotomicField p ℚ) := ⟨w, hwint⟩ with hw𝓞
  have hw𝓞p : w𝓞 ^ p = ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      := by
    refine hfinj ?_
    rw [map_pow, hαK]
    rw [show f w𝓞 = w from rfl, hw, pow_one]
  -- the Frobenius trick: α ≡ a mod π^{p−1}
  obtain ⟨a, ha⟩ := exists_int_sub_pow_prime_dvd (p := p) w𝓞
  rw [Ideal.mem_span_singleton] at ha
  rw [hw𝓞p] at ha
  obtain ⟨uu, huu⟩ := associated_zeta_sub_one_pow_prime hζ
  have hππp : (1 - hζ.toInteger) ^ (p - 1) ∣ ((p : 𝓞 (CyclotomicField p ℚ))) := by
    have h2 : (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ)) ^ (p - 1)
        = (1 - hζ.toInteger) ^ (p - 1) * (-1 : 𝓞 (CyclotomicField p ℚ)) ^ (p - 1)
        := by
      rw [show (hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) - 1 = (1 - hζ.toInteger) * (-1) from by
        ring, mul_pow]
    refine ⟨(-1 : 𝓞 (CyclotomicField p ℚ)) ^ (p - 1)
      * ((uu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)), ?_⟩
    rw [← huu, h2]
    ring
  have hcra : (1 - hζ.toInteger) ^ (p - 1)
      ∣ (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          - ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))) :=
    hππp.trans ha
  -- conjugate transport
  obtain ⟨uc, huc⟩ : Associated (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
      (1 - hζ.toInteger ^ (p - 1)) :=
    one_sub_pow_associated hζ (by omega) (by
      intro hdvd
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))
  have hconjdvd : ∀ (x : 𝓞 (CyclotomicField p ℚ)),
      (1 - hζ.toInteger) ^ (p - 1) ∣ x →
      (1 - hζ.toInteger) ^ (p - 1)
        ∣ ringOfIntegersComplexConj (CyclotomicField p ℚ) x := by
    intro x hx
    obtain ⟨t, ht⟩ := hx
    refine ⟨((uc : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ (p - 1)
      * ringOfIntegersComplexConj (CyclotomicField p ℚ) t, ?_⟩
    have h1 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) ht
    rw [map_mul, map_pow] at h1
    rw [show ringOfIntegersComplexConj (CyclotomicField p ℚ) (1 - hζ.toInteger)
        = 1 - hζ.toInteger ^ (p - 1) from by
      rw [map_sub, map_one, conjO_toInteger hζ], ← huc] at h1
    rw [h1, mul_pow]
    ring
  have hcrac : (1 - hζ.toInteger) ^ (p - 1)
      ∣ (ringOfIntegersComplexConj (CyclotomicField p ℚ)
            ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          - ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))) := by
    have h1 := hconjdvd _ hcra
    rwa [map_sub, show ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((a : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))
      from conjO_intCast a] at h1
  -- p ∣ a² − 1 in ℤ
  have hπ1le : (1 - hζ.toInteger)
      ∣ (1 - hζ.toInteger) ^ (p - 1) := dvd_pow_self _ (by omega)
  have hasq : (p : ℤ) ∣ a ^ 2 - 1 := by
    refine (one_sub_zeta_dvd_intCast_iff hζ (a ^ 2 - 1)).mp ?_
    have h1 : ((a ^ 2 - 1 : ℤ) : 𝓞 (CyclotomicField p ℚ))
        = ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))
            * (((a : ℤ) : 𝓞 (CyclotomicField p ℚ))
              - ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
          + ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * (((a : ℤ) : 𝓞 (CyclotomicField p ℚ))
              - ringOfIntegersComplexConj (CyclotomicField p ℚ)
                  ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
        := by
      push_cast
      linear_combination hαconj
    rw [h1]
    refine dvd_add (Dvd.dvd.mul_left ?_ _) (Dvd.dvd.mul_left ?_ _)
    · have h2 := (hπ1le.trans hcra)
      rw [show ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))
          - ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          = -(((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            - ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))) from by ring]
      exact h2.neg_right
    · have h2 := (hπ1le.trans hcrac)
      rw [show ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))
          - ringOfIntegersComplexConj (CyclotomicField p ℚ)
              ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          = -(ringOfIntegersComplexConj (CyclotomicField p ℚ)
              ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            - ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))) from by ring]
      exact h2.neg_right
  -- the case split: p ∣ (a−1)(a+1)
  have hpz : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hpri.out
  have hsplit : (p : ℤ) ∣ (a - 1) * (a + 1) := by
    rw [show (a - 1) * (a + 1) = a ^ 2 - 1 from by ring]
    exact hasq
  have hcast : ∀ b : ℤ, (p : ℤ) ∣ b →
      (1 - hζ.toInteger) ^ (p - 1) ∣ ((b : ℤ) : 𝓞 (CyclotomicField p ℚ)) := by
    intro b hb
    obtain ⟨k, hk⟩ := hb
    refine hππp.trans ⟨((k : ℤ) : 𝓞 (CyclotomicField p ℚ)), ?_⟩
    rw [hk]
    push_cast
    ring
  rcases hpz.dvd_mul.mp hsplit with hcase | hcase
  · -- CASE p ∣ a − 1: α ≡ 1 mod π^{p−1}; Kronecker forces α = 1, so ω + θ = 0
    have hα1 : (1 - hζ.toInteger) ^ (p - 1)
        ∣ (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1) := by
      have h1 := dvd_add hcra (hcast _ hcase)
      rwa [show ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          - ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))
          + (((a - 1 : ℤ) : ℤ) : 𝓞 (CyclotomicField p ℚ))
          = ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1 from by
        push_cast
        ring] at h1
    -- Kronecker: α is a root of unity
    set x : CyclotomicField p ℚ :=
      f ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) with hx
    have hxi : IsIntegral ℤ x := RingOfIntegers.isIntegral_coe _
    have hxconj : x * complexConj (CyclotomicField p ℚ) x = 1 := by
      rw [hx, show complexConj (CyclotomicField p ℚ)
          (f ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
          = f (ringOfIntegersComplexConj (CyclotomicField p ℚ)
              ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))) from
        (coe_ringOfIntegersComplexConj _ _).symm, ← map_mul, hαconj, map_one]
    have hnorm : ∀ φ : CyclotomicField p ℚ →+* ℂ, ‖φ x‖ = 1 := by
      intro φ
      have h1 : (φ x) * (starRingEnd ℂ) (φ x) = 1 := by
        rw [show (starRingEnd ℂ) (φ x)
            = φ (complexConj (CyclotomicField p ℚ) x) from by
          rw [complexEmbedding_complexConj], ← map_mul, hxconj, map_one]
      have h2 : ((Complex.normSq (φ x) : ℝ) : ℂ) = 1 := by
        rw [← Complex.mul_conj]
        exact h1
      have h3 : Complex.normSq (φ x) = 1 := by
        exact_mod_cast h2
      have h4 : ‖φ x‖ ^ 2 = 1 := by
        rw [← Complex.normSq_eq_norm_sq]
        exact h3
      nlinarith [norm_nonneg (φ x)]
    obtain ⟨n, hn0, hxn⟩ :=
      NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := CyclotomicField p ℚ)
        (A := ℂ) hxi hnorm
    have hαn : ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ n = 1
        := by
      refine hfinj ?_
      rw [map_pow, map_one]
      exact hxn
    have hα2p : ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        ^ (2 * p) = 1 :=
      CaseIIVandiverDescent.pow_2p_eq_one_of_pow_eq_one (by omega : p ≠ 2) hn0 hαn
    -- α^p = ±1
    have hβ : (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ p - 1)
        * (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ p + 1)
        = 0 := by
      rw [show 2 * p = p * 2 from mul_comm 2 p, pow_mul] at hα2p
      linear_combination hα2p
    have hπ2' : ¬ (1 - hζ.toInteger) ^ (p - 1) ∣ (2 : 𝓞 (CyclotomicField p ℚ)) := by
      intro h
      exact hπ2 ((dvd_pow_self _ (show p - 1 ≠ 0 from by omega)).trans h)
    rcases mul_eq_zero.mp hβ with hβ1 | hβ1
    · -- α^p = 1: α = ζ^c
      have hαp1 : ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ p
          = 1 := by linear_combination hβ1
      obtain ⟨c, hclt, hc⟩ :=
        hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hαp1
      rcases Nat.eq_zero_or_pos c with hc0 | hc0
      · -- α = 1 ⟹ ω + θ = 0, contradiction
        rw [hc0, pow_zero] at hc
        have hαD1 := hαD
        rw [← hc] at hαD1
        -- D = −ζ^{p−1}·N ⟹ (1+ζ^{p−1})(ω+θ) = 0
        have h5 : (1 + hζ.toInteger ^ (p - 1)) * (S.ω + S.θ) = 0 := by
          have hzeta1 : hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 := by
            rw [← pow_succ, show p - 1 + 1 = p from by omega, hpow]
          linear_combination hαD1 - S.θ * hzeta1
        rcases mul_eq_zero.mp h5 with h6 | h6
        · -- 1 + ζ^{p−1} = 0 forces p ∣ 2(p−1)
          have h7 : hζ.toInteger ^ (2 * (p - 1)) = 1 := by
            rw [show 2 * (p - 1) = (p - 1) * 2 from mul_comm _ _, pow_mul]
            have h8 : hζ.toInteger ^ (p - 1) = -1 := by linear_combination h6
            rw [h8]
            ring
          have h9 := (hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp h7
          rcases h9 with ⟨k, hk⟩
          have hk2 : p * k < p * 2 := by omega
          have hk3 : k < 2 := Nat.lt_of_mul_lt_mul_left hk2
          interval_cases k <;> omega
        · exact hNE h6
      · -- α = ζ^c, c ≠ 0: π² ∣ ζ^c − 1 is impossible
        obtain ⟨u₄, hu₄⟩ := one_sub_pow_associated hζ hp2 (j := c) (by
          intro hdvd
          exact absurd (Nat.le_of_dvd hc0 hdvd) (by omega))
        have h10 : (1 - hζ.toInteger) ^ 2
            ∣ (1 - hζ.toInteger ^ c) := by
          have h11 : (1 - hζ.toInteger) ^ 2 ∣ (1 - hζ.toInteger) ^ (p - 1) :=
            pow_dvd_pow _ (by omega)
          have h12 := h11.trans hα1
          rw [← hc] at h12
          rw [show (1 - hζ.toInteger ^ c : 𝓞 (CyclotomicField p ℚ))
              = -(hζ.toInteger ^ c - 1) from by ring]
          exact h12.neg_right
        rw [← hu₄] at h10
        have h13 : (1 - hζ.toInteger) * (1 - hζ.toInteger)
            ∣ (1 - hζ.toInteger) * ((u₄ : (𝓞 (CyclotomicField p ℚ))ˣ)
              : 𝓞 (CyclotomicField p ℚ)) := by
          rw [← sq]
          exact h10
        have h14 := (mul_dvd_mul_iff_left hπprime.ne_zero).mp h13
        exact hπprime.not_unit (isUnit_of_dvd_unit h14 u₄.isUnit)
    · -- α^p = −1: α = −ζ^c; π^{p−1} ∣ 1 + ζ^c is impossible
      have hαpm1 : ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ p
          = -1 := by linear_combination hβ1
      have hodd : Odd p := hpri.out.odd_of_ne_two (by omega)
      have hnegp : (-((αu : (𝓞 (CyclotomicField p ℚ))ˣ)
          : 𝓞 (CyclotomicField p ℚ))) ^ p = 1 := by
        rw [Odd.neg_pow hodd, hαpm1]
        ring
      obtain ⟨c, hclt, hc⟩ :=
        hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hnegp
      -- π^{p−1} ∣ 1 + ζ^c
      have h15 : (1 - hζ.toInteger) ^ (p - 1) ∣ (1 + hζ.toInteger ^ c) := by
        have h16 := hα1
        rw [show ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1
            = -(hζ.toInteger ^ c + 1) from by linear_combination hc] at h16
        rw [show (1 + hζ.toInteger ^ c : 𝓞 (CyclotomicField p ℚ))
            = -(-(hζ.toInteger ^ c + 1)) from by ring]
        exact h16.neg_right
      rcases Nat.eq_zero_or_pos c with hc0 | hc0
      · rw [hc0, pow_zero] at h15
        exact hπ2' (by
          rwa [show (1 + 1 : 𝓞 (CyclotomicField p ℚ)) = 2 from by norm_num] at h15)
      · -- 1 + ζ^c is a unit
        obtain ⟨u₅, hu₅⟩ := one_sub_pow_associated hζ hp2 (j := c) (by
          intro hdvd
          exact absurd (Nat.le_of_dvd hc0 hdvd) (by omega))
        obtain ⟨u₆, hu₆⟩ := one_sub_pow_associated hζ hp2 (j := 2 * c) (by
          intro hdvd
          rcases (Nat.Prime.dvd_mul hpri.out).mp hdvd with h | h
          · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
          · exact absurd (Nat.le_of_dvd hc0 h) (by omega))
        have hident : (1 + hζ.toInteger ^ c) * (1 - hζ.toInteger ^ c)
            = 1 - hζ.toInteger ^ (2 * c) := by
          rw [show 2 * c = c + c from by ring, pow_add]
          ring
        rw [← hu₅, ← hu₆] at hident
        have h17 : (1 - hζ.toInteger)
            * ((1 + hζ.toInteger ^ c) * ((u₅ : (𝓞 (CyclotomicField p ℚ))ˣ)
              : 𝓞 (CyclotomicField p ℚ)))
            = (1 - hζ.toInteger) * ((u₆ : (𝓞 (CyclotomicField p ℚ))ˣ)
              : 𝓞 (CyclotomicField p ℚ)) := by
          linear_combination hident
        have h18 := mul_left_cancel₀ hπprime.ne_zero h17
        have h19 : IsUnit (1 + hζ.toInteger ^ c) := by
          refine isUnit_of_mul_isUnit_left (y := ((u₅ : (𝓞 (CyclotomicField p ℚ))ˣ)
            : 𝓞 (CyclotomicField p ℚ))) ?_
          rw [h18]
          exact u₆.isUnit
        have h20 : (1 - hζ.toInteger) ∣ (1 + hζ.toInteger ^ c) :=
          (dvd_pow_self _ (show p - 1 ≠ 0 from by omega)).trans h15
        exact hπprime.not_unit (isUnit_of_dvd_unit h20 h19)
  · -- CASE p ∣ a + 1: the valuation kill via D(α+1) = (1−ζ^{p−1})(ω−θ)
    have hα1 : (1 - hζ.toInteger) ^ (p - 1)
        ∣ (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) + 1) := by
      have h1 := dvd_add hcra (hcast _ hcase)
      rwa [show ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          - ((a : ℤ) : 𝓞 (CyclotomicField p ℚ))
          + (((a + 1 : ℤ) : ℤ) : 𝓞 (CyclotomicField p ℚ))
          = ((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) + 1 from by
        push_cast
        ring] at h1
    have hzeta1 : hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 := by
      rw [← pow_succ, show p - 1 + 1 = p from by omega, hpow]
    -- D(α+1) = (1−ζ^{p−1})(ω−θ)
    have hDα : (S.ω + hζ.toInteger ^ (p - 1) * S.θ)
        * (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) + 1)
        = (1 - hζ.toInteger ^ (p - 1)) * (S.ω - S.θ) := by
      linear_combination hαD - S.θ * hzeta1
    have hdvd1 : (1 - hζ.toInteger) ^ p
        ∣ ((S.ω + hζ.toInteger ^ (p - 1) * S.θ)
          * (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) + 1)) := by
      have h21 : (1 - hζ.toInteger) ^ (1 + (p - 1))
          ∣ ((S.ω + hζ.toInteger ^ (p - 1) * S.θ)
            * (((αu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) + 1))
          := by
        rw [pow_add, pow_one]
        refine mul_dvd_mul ?_ hα1
        rw [← hu₂]
        exact Dvd.intro _ rfl
      rwa [show 1 + (p - 1) = p from by omega] at h21
    rw [hDα] at hdvd1
    -- cancel one π: π^{p−1} ∣ uc(ω−θ), hence π ∣ ω−θ
    rw [← huc] at hdvd1
    have hdvd2 : (1 - hζ.toInteger) * (1 - hζ.toInteger) ^ (p - 1)
        ∣ (1 - hζ.toInteger) * (((uc : (𝓞 (CyclotomicField p ℚ))ˣ)
          : 𝓞 (CyclotomicField p ℚ)) * (S.ω - S.θ)) := by
      rw [show (1 - hζ.toInteger) * ((1 - hζ.toInteger) ^ (p - 1))
          = (1 - hζ.toInteger) ^ p from by
        rw [← pow_succ']
        congr 1
        omega]
      calc (1 - hζ.toInteger) ^ p
          ∣ (1 - hζ.toInteger) * ((uc : (𝓞 (CyclotomicField p ℚ))ˣ)
            : 𝓞 (CyclotomicField p ℚ)) * (S.ω - S.θ) := hdvd1
        _ = (1 - hζ.toInteger) * (((uc : (𝓞 (CyclotomicField p ℚ))ˣ)
            : 𝓞 (CyclotomicField p ℚ)) * (S.ω - S.θ)) := by ring
    have hdvd3 := (mul_dvd_mul_iff_left hπprime.ne_zero).mp hdvd2
    have hdvd4 : (1 - hζ.toInteger)
        ∣ ((uc : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * (S.ω - S.θ) :=
      (dvd_pow_self _ (show p - 1 ≠ 0 from by omega)).trans hdvd3
    have hdvd5 : (1 - hζ.toInteger) ∣ (S.ω - S.θ) := by
      rcases hπprime.dvd_mul.mp hdvd4 with h | h
      · exact absurd (isUnit_of_dvd_unit h uc.isUnit) hπprime.not_unit
      · exact h
    -- π ∣ ω+θ and π ∣ ω−θ ⟹ π ∣ 2ω ⟹ π ∣ ω, contradiction
    have hdvd6 := pi_dvd_omega_add_theta S hp2
    have hdvd7 : (1 - hζ.toInteger) ∣ (2 * S.ω) := by
      rw [show (2 * S.ω : 𝓞 (CyclotomicField p ℚ))
          = (S.ω + S.θ) + (S.ω - S.θ) from by ring]
      exact dvd_add hdvd6 hdvd5
    rcases hπprime.dvd_mul.mp hdvd7 with h | h
    · exact hπ2 h
    · exact S.hlamω h

end FltVandiver.Descent92
