import FltVandiver.Descent92Step3
open CyclotomicNT

/-!
# Descent92, file 5 of 9 — the second factorization (Washington pp. 174–175)

From the step-3 pair `ω + ζ^{±a}θ = (1−ζ^{±a})·η_a·ρ_{±a}^p` (`ρ_{−a} = conj ρ_a`) and
step 1, the difference `ρ_a^p − ρ_{−a}^p` is DEEP (`v_π = 2m−p`); the product
factorization `∏ᵢ(ρ_a − ζⁱρ_{−a})` then yields (after a `ζ`-power renormalization of
`ρ_a`, harmless since `(ζ^cρ_a)^p = ρ_a^p`) the second-level decomposition
`(ρ_a − ζρ_{−a})/(1−ζ) = ηt_a·μ_a^p` with `ηt_a, μ_a` real, hence

  `ρ_a ≡ ηt_a μ_a^p  mod (1−ζ)^{2m−2p}`.

The Kummer input `U = (η_a ηt_a^p)/(η_b ηt_b^p) ≡ (μ_b/μ_a)^{p²}` follows, feeding
(Assumption II now lives in the 9.5 route — `Descent95.assumption_II_95`.) -/

namespace FltVandiver.Descent92

open scoped NumberField nonZeroDivisors
open NumberField NumberField.IsCMField Polynomial

variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  [NumberField.IsCMField (CyclotomicField p ℚ)]

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **The deep difference** (Washington p. 174): from the step-3 pair and step 1,
`λ_a·η_a·(ρ_a^p − ρ_{−a}^p) = (ζ^a − ζ^{−a})·(ω + θ)`. -/
theorem second_difference_identity {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 2 < p) {a : ℕ}
    (_ha : a.Coprime p) {ηa : (𝓞 (CyclotomicField p ℚ))ˣ}
    {ρa : 𝓞 (CyclotomicField p ℚ)}
    (heqa : S.ω + hζ.toInteger ^ a * S.θ
      = (1 - hζ.toInteger ^ a)
        * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρa ^ p)
    (heqma : S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ
      = (1 - hζ.toInteger ^ (a * (p - 1)))
        * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p) :
    (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
        * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (ρa ^ p - (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p)
      = (hζ.toInteger ^ a - hζ.toInteger ^ (a * (p - 1))) * (S.ω + S.θ) := by
  -- ζ^a·ζ^{a(p−1)} = ζ^{ap} = 1
  have hzz : hζ.toInteger ^ a * hζ.toInteger ^ (a * (p - 1)) = 1 := by
    rw [← pow_add, show a + a * (p - 1) = a * p from by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega]
      ring]
    rw [mul_comm, pow_mul]
    have hpow : hζ.toInteger ^ p = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
        (CyclotomicField p ℚ)
      have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          hζ.toInteger = ζ := hζ.coe_toInteger
      rw [map_pow, map_one, ht]
      exact hζ.pow_eq_one
    rw [hpow, one_pow]
  -- multiply the equations crosswise and subtract (the ζ^a·ζ^{−a}-terms cancel)
  linear_combination (-(1 - hζ.toInteger ^ (a * (p - 1)))) * heqa
    + (1 - hζ.toInteger ^ a) * heqma

/-- The step-3 witness generates the original factor ideal: `(ρ_a) = B_a`. -/
theorem span_rho_eq_of_step3 {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) {a : ℕ} (hpa : ¬ p ∣ a)
    {ηa : (𝓞 (CyclotomicField p ℚ))ˣ} {ρa : 𝓞 (CyclotomicField p ℚ)}
    {Ba : Ideal (𝓞 (CyclotomicField p ℚ))}
    (heqa : S.ω + hζ.toInteger ^ a * S.θ
      = (1 - hζ.toInteger ^ a)
        * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρa ^ p)
    (hBa : Ideal.span {S.ω + hζ.toInteger ^ a * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Ba ^ p) :
    Ideal.span {ρa} = Ba := by
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  -- span{N} = 𝔭·span{ρa}^p
  have h1 : Ideal.span {S.ω + hζ.toInteger ^ a * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}
        * (Ideal.span {ρa}) ^ p := by
    rw [heqa]
    have hassoc : Associated
        ((1 - hζ.toInteger) * ρa ^ p : 𝓞 (CyclotomicField p ℚ))
        ((1 - hζ.toInteger ^ a)
          * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρa ^ p)
        := by
      obtain ⟨u1, hu1⟩ := one_sub_pow_associated hζ hp hpa
      refine ⟨u1 * ηa, ?_⟩
      rw [← hu1]
      push_cast [Units.val_mul]
      ring
    rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc,
      ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow]
  rw [h1] at hBa
  have h𝔭ne : Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}
      ≠ (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hπprime.ne_zero
  exact pow_left_injective hpri.out.ne_zero (mul_left_cancel₀ h𝔭ne hBa)

/-- **The second product-span equation**: `∏_{ζ'}(ρ_a − ζ'ρ̄_a) = 𝔭^{2m−p}·B₀^p` as
ideals, where `B₀` is the deep ideal of the first decomposition. -/
theorem second_prod_span {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) {a : ℕ} (ha : a.Coprime p)
    {ηa : (𝓞 (CyclotomicField p ℚ))ˣ} {ρa : 𝓞 (CyclotomicField p ℚ)}
    (heqa : S.ω + hζ.toInteger ^ a * S.θ
      = (1 - hζ.toInteger ^ a)
        * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρa ^ p)
    (heqma : S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ
      = (1 - hζ.toInteger ^ (a * (p - 1)))
        * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p)
    {B₀ : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hB₀ : Ideal.span {S.ω + S.θ}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - (p - 1))
        * B₀ ^ p) :
    ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
    = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - p)
      * B₀ ^ p := by
  classical
  have hpa : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hpri.out).mp ha.symm
  have hdiff := second_difference_identity S hp ha heqa heqma
  -- the root-difference ζ^a − ζ^{a(p−1)} is a π-associate
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hamem : hζ.toInteger ^ a ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
      hpow, one_pow]
  have hamem2 : hζ.toInteger ^ (a * (p - 1))
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul,
      show a * (p - 1) * p = p * (a * (p - 1)) from by ring, pow_mul, hpow, one_pow]
  have hne : hζ.toInteger ^ a ≠ hζ.toInteger ^ (a * (p - 1)) := by
    intro heq
    have h2 : a * (p - 1) = a + (a * (p - 1) - a) := by
      have := Nat.le_mul_of_pos_right a (show 0 < p - 1 by omega)
      omega
    have h1 : hζ.toInteger ^ (a * (p - 1) - a) = 1 := by
      rw [h2, pow_add] at heq
      have hz0 : hζ.toInteger ^ a ≠ 0 :=
        pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.ne_zero (by omega))
      have heq2 : hζ.toInteger ^ a * 1
          = hζ.toInteger ^ a * hζ.toInteger ^ (a * (p - 1) - a) := by
        rw [mul_one]
        exact heq
      exact (mul_left_cancel₀ hz0 heq2).symm
    have h3 := (hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp h1
    have h4 : a * (p - 1) - a = a * (p - 2) := by
      have h5 := hpri.out.two_le
      zify [show 1 ≤ p from by omega, show 2 ≤ p from h5,
        show a ≤ a * (p - 1) from Nat.le_mul_of_pos_right a (by omega)]
      ring
    rw [h4] at h3
    rcases (Nat.Prime.dvd_mul hpri.out).mp h3 with h | h
    · exact hpa h
    · rcases (by omega : 0 < p - 2 ∨ p - 2 = 0) with h6 | h6
      · exact absurd (Nat.le_of_dvd h6 h) (by omega)
      · omega
  have hassocd : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
      (hζ.toInteger ^ a - hζ.toInteger ^ (a * (p - 1))) :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr hamem) (Finset.mem_coe.mpr hamem2) hne
  -- assemble the span equation and cancel 𝔭²
  set 𝔭 : Ideal (𝓞 (CyclotomicField p ℚ)) :=
    Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} with h𝔭
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  -- span{ρ^p − ρ̄^p} = ∏ span-factors
  have hprodform : Ideal.span {ρa ^ p
        - (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p}
      = ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa} := by
    rw [Submodule.prod_span_singleton,
      hζ.toInteger_isPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul _ _ hpri.out.pos]
  -- the big balance: 𝔭²·∏ = 𝔭^{2m−p+2}·B₀^p, then cancel
  have hbal : 𝔭 ^ 2 * (∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa})
      = 𝔭 ^ 2 * (𝔭 ^ (2 * S.m - p) * B₀ ^ p) := by
    have hlam : 𝔭 ^ 2 = Ideal.span
        {(1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))} := by
      rw [← Ideal.span_singleton_mul_span_singleton, sq, h𝔭,
        ← Ideal.span_singleton_eq_span_singleton.mpr
          (one_sub_pow_associated hζ hp hpa),
        ← Ideal.span_singleton_eq_span_singleton.mpr
          (one_sub_pow_associated hζ hp (by
            intro hdvd
            rcases (Nat.Prime.dvd_mul hpri.out).mp hdvd with h | h
            · exact hpa h
            · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)))]
    calc 𝔭 ^ 2 * (∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
          Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa})
        = Ideal.span {(1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
            * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * (ρa ^ p
              - (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p)} := by
          rw [hlam, ← hprodform, Ideal.span_singleton_mul_span_singleton]
          refine Ideal.span_singleton_eq_span_singleton.mpr ?_
          rw [show (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
              * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * (ρa ^ p - (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p)
            = ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
                * (ρa ^ p
                  - (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p))
            from by ring]
          exact associated_unit_mul_right _ _ ηa.isUnit
      _ = Ideal.span {(hζ.toInteger ^ a - hζ.toInteger ^ (a * (p - 1)))
            * (S.ω + S.θ)} := by
          rw [hdiff]
      _ = 𝔭 ^ 2 * (𝔭 ^ (2 * S.m - p) * B₀ ^ p) := by
          rw [← Ideal.span_singleton_mul_span_singleton,
            ← Ideal.span_singleton_eq_span_singleton.mpr hassocd, hB₀]
          rw [show (Ideal.span {(hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))})
              = 𝔭 from by
            rw [h𝔭]
            refine Ideal.span_singleton_eq_span_singleton.mpr ?_
            exact ⟨-1, by
              simp only [Units.val_neg, Units.val_one]
              ring⟩]
          have hub : p ≤ 2 * S.m := by
            have h4 : 2 ∣ p - 1 := by
              have hodd := hpri.out.odd_of_ne_two (by omega)
              rw [Nat.odd_iff] at hodd
              omega
            have h1 : p * (p - 1) / 2 = p * ((p - 1) / 2) := Nat.mul_div_assoc p h4
            have h2 : p ≤ p * ((p - 1) / 2) :=
              Nat.le_mul_of_pos_right p (by omega)
            have h7 := S.hm
            omega
          have hexpeq : (2 * S.m - (p - 1)) + 1 = 2 + (2 * S.m - p) := by omega
          rw [← mul_assoc, ← mul_assoc, ← pow_succ', ← pow_add, hexpeq, pow_add,
            mul_assoc]
  have h𝔭ne : 𝔭 ^ 2 ≠ (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
    refine pow_ne_zero _ ?_
    rw [h𝔭, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hπprime.ne_zero
  exact mul_left_cancel₀ h𝔭ne hbal

open scoped Classical in
/-- **The second-level factor extraction** (Washington p. 175): the `ρ`-difference
factors decompose as `𝔭^{e}·C^p` with `𝔭 ∤ C`, exactly one factor deep
(`e = 2m−2p+2` there, `e = 1` elsewhere). -/
theorem exists_second_factor_ideals {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 3 < p)
    {ρa : 𝓞 (CyclotomicField p ℚ)} {B₀ : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hπρc : ¬ (1 - hζ.toInteger) ∣ ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)
    (hρcop : IsCoprime (Ideal.span {ρa})
      (Ideal.span {ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}))
    (h𝔭B₀ : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ B₀)
    (_hρ0 : ρa ≠ 0)
    (hprod : ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - p)
        * B₀ ^ p) :
    ∃ (C : 𝓞 (CyclotomicField p ℚ) → Ideal (𝓞 (CyclotomicField p ℚ)))
      (i₀ : 𝓞 (CyclotomicField p ℚ)),
      i₀ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))
      ∧ (∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
          Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
            = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))})
                ^ (if ζ' = i₀ then 2 * S.m - 2 * p + 1 else 1) * (C ζ') ^ p)
      ∧ (∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
          ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ C ζ') := by
  classical
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  set 𝔭 : Ideal (𝓞 (CyclotomicField p ℚ)) := Ideal.span {(1 - hζ.toInteger)} with h𝔭
  have h𝔭prime : Prime 𝔭 :=
    Ideal.prime_of_isPrime (by
      simpa [h𝔭, Ideal.span_singleton_eq_bot] using hπprime.ne_zero)
      ((Ideal.span_singleton_prime hπprime.ne_zero).mpr hπprime)
  have hB₀0 : B₀ ≠ 0 := fun h0 => h𝔭B₀ (h0 ▸ dvd_zero 𝔭)
  -- factors are nonzero
  have hfac0 : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa ≠ 0 := by
    intro ζ' hζ'mem h0
    have h1 : ∏ ζ'' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        Ideal.span {ρa - ζ'' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
        = 0 := by
      refine Finset.prod_eq_zero hζ'mem ?_
      rw [h0, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rw [hprod] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact (pow_ne_zero _ h𝔭prime.ne_zero) h2
    · exact (pow_ne_zero _ hB₀0) h2
  -- per-factor multiplicity strip
  have hstrip : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      ∃ (e : ℕ) (Cz : Ideal (𝓞 (CyclotomicField p ℚ))),
        Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
          = 𝔭 ^ e * Cz ∧ ¬ 𝔭 ∣ Cz := by
    intro ζ' hζ'mem
    have hne : Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
        ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hfac0 ζ' hζ'mem
    have hfin : FiniteMultiplicity 𝔭 (Ideal.span
        {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}) :=
      FiniteMultiplicity.of_prime_left h𝔭prime hne
    obtain ⟨Cz, hC1, hC2⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    exact ⟨_, Cz, hC1, hC2⟩
  choose! e C hC1 hC2 using hstrip
  -- product and cancel
  have hprodC : 𝔭 ^ (∑ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), e ζ')
      * (∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), C ζ')
      = 𝔭 ^ (2 * S.m - p) * B₀ ^ p := by
    rw [← hprod, Finset.prod_congr rfl (fun ζ' h => hC1 ζ' h),
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have h𝔭C : ¬ 𝔭 ∣ ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), C ζ' := by
    intro hdvd
    obtain ⟨ζ', hζ'mem, hdvd'⟩ := h𝔭prime.exists_mem_finset_dvd hdvd
    exact hC2 ζ' hζ'mem hdvd'
  have h𝔭B : ¬ 𝔭 ∣ B₀ ^ p := fun hdvd => h𝔭B₀ (h𝔭prime.dvd_of_dvd_pow hdvd)
  obtain ⟨hsum, hCprod⟩ := prime_pow_mul_cancel h𝔭prime h𝔭C h𝔭B hprodC
  -- each exponent is ≥ 1
  have hcard := hζ.toInteger_isPrimitiveRoot.card_nthRootsFinset
  have hub : p * (p - 1) ≤ 2 * S.m := by
    have h4 : 2 ∣ p - 1 := by
      have hodd := hpri.out.odd_of_ne_two (by omega)
      rw [Nat.odd_iff] at hodd
      omega
    have h6 : 2 ∣ p * (p - 1) := Dvd.dvd.mul_left h4 p
    have h7 := S.hm
    omega
  have hub2 : 2 * p < 2 * S.m := by
    have h1 : 2 * p < p * (p - 1) := by
      have h2 : 4 ≤ p - 1 + 1 := by omega
      calc 2 * p < (p - 1) * p := by
            refine Nat.mul_lt_mul_of_lt_of_le ?_ le_rfl (by omega)
            omega
        _ = p * (p - 1) := mul_comm _ _
    omega
  -- some factor has e ≥ 1, hence (by the difference congruences) all do
  have hsome : ∃ ζ₀ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), 1 ≤ e ζ₀ := by
    by_contra hall
    push Not at hall
    have h1 : ∑ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), e ζ' = 0 := by
      refine Finset.sum_eq_zero fun ζ' h => ?_
      have := hall ζ' h
      omega
    omega
  have hone : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), 1 ≤ e ζ' := by
    obtain ⟨ζ₀, hζ₀mem, hζ₀e⟩ := hsome
    intro ζ' hζ'mem
    by_contra he0
    have he0' : e ζ' = 0 := by omega
    -- π divides the ζ₀-factor, and the difference, hence the ζ'-factor: contradiction
    have hπ0 : (1 - hζ.toInteger)
        ∣ (ρa - ζ₀ * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
      have h1 : 𝔭 ^ 1 ∣ Ideal.span
          {ρa - ζ₀ * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa} := by
        rw [hC1 ζ₀ hζ₀mem]
        exact dvd_mul_of_dvd_left (pow_dvd_pow 𝔭 hζ₀e) _
      rw [pow_one, h𝔭, Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at h1
      exact h1
    have hπd : (1 - hζ.toInteger)
        ∣ ((ζ₀ - ζ') * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
      by_cases hzz : ζ₀ = ζ'
      · rw [hzz, sub_self, zero_mul]
        exact dvd_zero _
      · refine Dvd.dvd.mul_right ?_ _
        have hassoc :=
          hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
            hpri.out (Finset.mem_coe.mpr hζ₀mem) (Finset.mem_coe.mpr hζ'mem) hzz
        exact (Dvd.dvd.trans ⟨-1, by ring⟩ hassoc.dvd)
    have hπ' : (1 - hζ.toInteger)
        ∣ (ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
      have h3 : ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa
          = (ρa - ζ₀ * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)
            + (ζ₀ - ζ') * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa := by
        ring
      rw [h3]
      exact dvd_add hπ0 hπd
    -- but e ζ' = 0 means 𝔭 ∤ the span
    have h4 : 𝔭 ∣ Ideal.span
        {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa} := by
      rw [h𝔭, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
      exact hπ'
    rw [hC1 ζ' hζ'mem, he0', pow_zero, one_mul] at h4
    exact hC2 ζ' hζ'mem h4
  -- at most one factor is deep
  have hdeep_unique : ∀ ζ₁ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      ∀ ζ₂ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), ζ₁ ≠ ζ₂ →
      ¬ (2 ≤ e ζ₁ ∧ 2 ≤ e ζ₂) := by
    rintro ζ₁ h₁ ζ₂ h₂ hne ⟨hd₁, hd₂⟩
    have hπ2 : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), 2 ≤ e ζ' →
        (1 - hζ.toInteger) ^ 2
        ∣ (ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
      intro ζ' hmem hd
      have h1 : 𝔭 ^ 2 ∣ Ideal.span
          {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa} := by
        rw [hC1 ζ' hmem]
        exact Dvd.dvd.mul_right (pow_dvd_pow 𝔭 hd) _
      rwa [h𝔭, Ideal.span_singleton_pow, Ideal.dvd_span_singleton,
        Ideal.mem_span_singleton] at h1
    have hd1' := hπ2 ζ₁ h₁ hd₁
    have hd2' := hπ2 ζ₂ h₂ hd₂
    have hdiff2 : (1 - hζ.toInteger) ^ 2
        ∣ ((ζ₂ - ζ₁) * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
      have h3 : (ζ₂ - ζ₁) * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa
          = (ρa - ζ₁ * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)
            - (ρa - ζ₂ * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
        ring
      rw [h3]
      exact dvd_sub hd1' hd2'
    have hassoc :=
      hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        hpri.out (Finset.mem_coe.mpr h₂) (Finset.mem_coe.mpr h₁) (Ne.symm hne)
    obtain ⟨v, hv⟩ := hassoc
    have hπne2 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ≠ 0 := hπprime.ne_zero
    have h7 : (ζ₂ - ζ₁) * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa
        = -((1 - hζ.toInteger)
          * (((v : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)) := by
      rw [← hv]
      ring
    rw [h7, dvd_neg, sq] at hdiff2
    have h8 := (mul_dvd_mul_iff_left hπne2).mp hdiff2
    rcases hπprime.dvd_mul.mp h8 with h9 | h9
    · exact hπprime.not_unit (isUnit_of_dvd_unit h9 v.isUnit)
    · exact hπρc h9
  -- the deep index exists (else the sum is too small)
  have hdeepex : ∃ i₀ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), 2 ≤ e i₀ := by
    by_contra hall
    push Not at hall
    have h1 : ∑ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), e ζ' ≤ p := by
      calc ∑ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), e ζ'
          ≤ ∑ _ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), 1 := by
            refine Finset.sum_le_sum fun ζ' h => ?_
            have := hall ζ' h
            omega
        _ = p := by
            rw [Finset.sum_const, smul_eq_mul, mul_one, hcard]
    omega
  obtain ⟨i₀, hi₀mem, hi₀d⟩ := hdeepex
  -- the deep exponent and the others
  have hothers : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), ζ' ≠ i₀ →
      e ζ' = 1 := by
    intro ζ' hmem hne'
    have h1 := hone ζ' hmem
    have h2 := hdeep_unique ζ' hmem i₀ hi₀mem hne'
    have h3 : ¬ (2 ≤ e ζ') := fun hh => h2 ⟨hh, hi₀d⟩
    omega
  have hei₀ : e i₀ = 2 * S.m - 2 * p + 1 := by
    have hsum2 : ∑ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), e ζ'
        = e i₀ + (p - 1) := by
      rw [← Finset.add_sum_erase _ _ hi₀mem]
      congr 1
      rw [Finset.sum_congr rfl (fun ζ' h => hothers ζ' (Finset.mem_of_mem_erase h)
        (Finset.ne_of_mem_erase h))]
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hi₀mem,
        hcard]
    omega
  -- pairwise coprimality of the C's (the 𝔮-argument at the ρ-level)
  have hpairC : ∀ a ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      ∀ b ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), a ≠ b →
      IsCoprime (C a) (C b) := by
    intro za hza zb hzb hab
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hsup
    obtain ⟨𝔮, h𝔮max, h𝔮⟩ := Ideal.exists_le_maximal _ hsup
    have hCa : C za ≤ 𝔮 := le_trans le_sup_left h𝔮
    have hCb : C zb ≤ 𝔮 := le_trans le_sup_right h𝔮
    have hfa : ρa - za * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa ∈ 𝔮 := by
      have h1 : Ideal.span
          {ρa - za * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa} ≤ C za := by
        rw [hC1 za hza]
        exact Ideal.mul_le_left
      exact hCa (h1 (Ideal.mem_span_singleton_self _))
    have hfb : ρa - zb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa ∈ 𝔮 := by
      have h1 : Ideal.span
          {ρa - zb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa} ≤ C zb := by
        rw [hC1 zb hzb]
        exact Ideal.mul_le_left
      exact hCb (h1 (Ideal.mem_span_singleton_self _))
    have hdiff : (zb - za) * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa
        ∈ 𝔮 := by
      have h2 : (zb - za) * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa
          = (ρa - za * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)
            - (ρa - zb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
        ring
      rw [h2]
      exact sub_mem hfa hfb
    rcases h𝔮max.isPrime.mem_or_mem hdiff with h2 | h2
    · -- the root-difference forces 𝔮 = 𝔭, contradicting 𝔭 ∤ C
      have hassoc :=
        hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          hpri.out (Finset.mem_coe.mpr hzb) (Finset.mem_coe.mpr hza) (Ne.symm hab)
      have hπ𝔮 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔮 := by
        obtain ⟨u, hu⟩ := hassoc
        have h3 : (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
            = (zb - za) * ((u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)
              : 𝓞 (CyclotomicField p ℚ)) := by
          rw [← hu, mul_assoc, show ((u : (𝓞 (CyclotomicField p ℚ))ˣ)
              : 𝓞 (CyclotomicField p ℚ))
              * ((u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1 from
            by rw [← Units.val_mul, mul_inv_cancel, Units.val_one], mul_one]
        rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
            = -(hζ.toInteger - 1) from by ring, h3]
        exact neg_mem (Ideal.mul_mem_right _ _ h2)
      have h𝔭max : 𝔭.IsMaximal :=
        Ideal.IsPrime.isMaximal
          ((Ideal.span_singleton_prime hπprime.ne_zero).mpr hπprime)
          (by simpa [h𝔭, Ideal.span_singleton_eq_bot] using hπprime.ne_zero)
      have h𝔭le : 𝔭 ≤ 𝔮 := by
        rw [h𝔭, Ideal.span_le]
        simpa using hπ𝔮
      have h𝔮eq : 𝔮 = 𝔭 := (h𝔭max.eq_of_le h𝔮max.ne_top h𝔭le).symm
      exact hC2 za hza ((Ideal.dvd_iff_le).mpr (h𝔮eq ▸ hCa))
    · -- ρ̄ ∈ 𝔮 forces ρ ∈ 𝔮, contradicting their coprimality
      have hρ𝔮 : ρa ∈ 𝔮 := by
        have h3 : ρa = (ρa - za * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)
            + za * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa := by ring
        rw [h3]
        exact add_mem hfa (Ideal.mul_mem_left _ _ h2)
      have h4 : (⊤ : Ideal (𝓞 (CyclotomicField p ℚ))) ≤ 𝔮 := by
        rw [← Ideal.isCoprime_iff_sup_eq.mp hρcop]
        refine sup_le ?_ ?_ <;> rw [Ideal.span_le]
        · simpa using hρ𝔮
        · simpa using h2
      exact h𝔮max.ne_top (top_le_iff.mp h4)
  -- extract the p-th powers
  have hex := Finset.exists_eq_pow_of_mul_eq_pow_of_coprime hpairC hCprod
  choose! D hD using hex
  refine ⟨D, i₀, hi₀mem, ?_, ?_⟩
  · intro ζ' hmem
    by_cases h1 : ζ' = i₀
    · rw [if_pos h1, hC1 ζ' hmem, h1, hei₀, ← hD i₀ hi₀mem]
    · rw [if_neg h1, hC1 ζ' hmem, hothers ζ' hmem h1, ← hD ζ' hmem]
  · intro ζ' hmem hdvd
    have h1 : 𝔭 ∣ C ζ' := by
      rw [hD ζ' hmem]
      exact hdvd.trans (dvd_pow_self _ (by omega : p ≠ 0))
    exact hC2 ζ' hmem h1
omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- The conjugate of `ζ^c·x` is `ζ^{c(p−1)}·conj x`. -/
theorem conjO_zeta_pow_mul {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (c : ℕ) (x : 𝓞 (CyclotomicField p ℚ)) :
    ringOfIntegersComplexConj (CyclotomicField p ℚ) (hζ.toInteger ^ c * x)
      = hζ.toInteger ^ (c * (p - 1))
        * ringOfIntegersComplexConj (CyclotomicField p ℚ) x := by
  rw [map_mul, map_pow, conjO_toInteger hζ, ← pow_mul, mul_comm (p - 1) c]

/-- **The ζ-normalization** (Washington p. 175): adjust the step-3 witness by a `ζ`-power
(preserving its `p`-th power, hence all step-3 equations) so the deep factor lands at
`ζ' = 1`: `π^{2m−2p+1} ∣ ρ' − conj ρ'`. -/
theorem exists_normalized_witness {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 3 < p)
    {ρa : 𝓞 (CyclotomicField p ℚ)} {B₀ : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hπρc : ¬ (1 - hζ.toInteger) ∣ ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)
    (hρcop : IsCoprime (Ideal.span {ρa})
      (Ideal.span {ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}))
    (h𝔭B₀ : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ B₀)
    (hρ0 : ρa ≠ 0)
    (hprod : ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        Ideal.span {ρa - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - p)
        * B₀ ^ p) :
    ∃ ρ' : 𝓞 (CyclotomicField p ℚ),
      ρ' ^ p = ρa ^ p
      ∧ (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ') ^ p
          = (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p
      ∧ (1 - hζ.toInteger) ^ (2 * S.m - 2 * p + 1)
          ∣ (hζ.toInteger ^ 0 * ρ'
              - ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ') := by
  classical
  haveI : Fact p.Prime := hpri
  obtain ⟨D, i₀, hi₀mem, hD1, hD2⟩ :=
    exists_second_factor_ideals S hp hπρc hρcop h𝔭B₀ hρ0 hprod
  obtain ⟨k₀, hk₀lt, hk₀⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one
    ((Polynomial.mem_nthRootsFinset hpri.out.pos 1).1 hi₀mem)
  -- choose c with 2c ≡ p − k₀ (mod p), via ZMod
  have h2ne : ((2 : ZMod p)) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    have h2 := (ZMod.natCast_eq_zero_iff 2 p).mp h1
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  set cz : ZMod p := ((p - k₀ : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ with hcz
  set c : ℕ := cz.val with hcdef
  -- the key exponent congruence: c(p−1) ≡ c + k₀ (mod p)
  have hexp_zmod : ((c * (p - 1) : ℕ) : ZMod p) = ((c + k₀ : ℕ) : ZMod p) := by
    push_cast
    have hp1 : (((p - 1 : ℕ)) : ZMod p) = -1 := by
      have h3 : (((p - 1 : ℕ) : ZMod p)) + 1 = 0 := by
        rw [show ((1 : ZMod p)) = ((1 : ℕ) : ZMod p) from by push_cast; rfl,
          ← Nat.cast_add, show p - 1 + 1 = p from by omega, ZMod.natCast_self]
      linear_combination h3
    rw [hp1]
    -- −c = c + k₀ ⟺ 2c = −k₀; and 2·cz = p − k₀ = −k₀
    have h4 : (2 : ZMod p) * cz = ((p - k₀ : ℕ) : ZMod p) := by
      rw [hcz]
      field_simp
    have h5 : (((p - k₀ : ℕ)) : ZMod p) = -((k₀ : ℕ) : ZMod p) := by
      have h6 : (((p - k₀ : ℕ) : ZMod p)) + ((k₀ : ℕ) : ZMod p) = 0 := by
        rw [← Nat.cast_add, show p - k₀ + k₀ = p from by omega, ZMod.natCast_self]
      linear_combination h6
    have h7 : ((c : ℕ) : ZMod p) = cz := by
      rw [hcdef, ZMod.natCast_val, ZMod.cast_id]
    rw [h7]
    linear_combination -h4 - h5
  have hexp : (c * (p - 1)) % p = (c + k₀) % p := by
    have h3 := congrArg ZMod.val hexp_zmod
    rwa [ZMod.val_natCast, ZMod.val_natCast] at h3
  -- the normalized witness ρ' := ζ^c·ρ
  refine ⟨hζ.toInteger ^ c * ρa, ?_, ?_, ?_⟩
  · rw [mul_pow, ← pow_mul, toInteger_pow_eq_of_mod hζ
      (show (c * p) % p = 0 % p from by simp [Nat.mul_mod_left]), pow_zero, one_mul]
  · rw [conjO_zeta_pow_mul hζ, mul_pow, ← pow_mul,
      toInteger_pow_eq_of_mod hζ
        (show (c * (p - 1) * p) % p = 0 % p from by
          rw [show c * (p - 1) * p = 0 + (c * (p - 1)) * p from by ring,
            Nat.add_mul_mod_self_right]),
      pow_zero, one_mul]
  · -- transport the deep factor
    rw [pow_zero, one_mul, conjO_zeta_pow_mul hζ]
    have hsplit : hζ.toInteger ^ (c * (p - 1))
        = hζ.toInteger ^ c * hζ.toInteger ^ k₀ := by
      rw [← pow_add]
      exact toInteger_pow_eq_of_mod hζ hexp
    have hkey : hζ.toInteger ^ c * ρa
        - hζ.toInteger ^ (c * (p - 1))
          * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa
        = hζ.toInteger ^ c
          * (ρa - i₀ * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
      rw [hsplit, hk₀]
      ring
    rw [hkey]
    -- the i₀-factor is deep
    have hdeep : (1 - hζ.toInteger) ^ (2 * S.m - 2 * p + 1)
        ∣ (ρa - i₀ * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
      have h1 := hD1 i₀ hi₀mem
      rw [if_pos rfl] at h1
      have h2 : (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))})
          ^ (2 * S.m - 2 * p + 1)
          ∣ Ideal.span {ρa - i₀ * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
          := by
        rw [h1]
        exact Dvd.intro _ rfl
      rwa [Ideal.span_singleton_pow, Ideal.dvd_span_singleton,
        Ideal.mem_span_singleton] at h2
    exact hdeep.mul_left _

set_option maxHeartbeats 1000000 in -- heavy elaboration: exceeds the default heartbeat budget
/-- **The second-level congruence** (Washington p. 175): from the normalized witness,
`ρ' ≡ ηt·μ^p mod π^{2m−2p}` with `ηt` a real unit and `μ` real — THE KUMMER INPUT SHAPE. -/
theorem second_level_congruence {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 3 < p)
    (hvand : IsVandiverPrime p)
    {ρ' : 𝓞 (CyclotomicField p ℚ)} {B₀ : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hπρc : ¬ (1 - hζ.toInteger) ∣ ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ')
    (hρcop : IsCoprime (Ideal.span {ρ'})
      (Ideal.span {ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'}))
    (h𝔭B₀ : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ B₀)
    (hρ0 : ρ' ≠ 0)
    (hprod : ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        Ideal.span {ρ' - ζ' * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - p)
        * B₀ ^ p)
    (hdeep : (1 - hζ.toInteger) ^ (2 * S.m - 2 * p + 1)
      ∣ (ρ' - ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ')) :
    ∃ (ηt : (𝓞 (CyclotomicField p ℚ))ˣ) (μ : 𝓞 (CyclotomicField p ℚ)),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((ηt : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = ((ηt : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      ∧ ringOfIntegersComplexConj (CyclotomicField p ℚ) μ = μ
      ∧ (1 - hζ.toInteger) ^ (2 * S.m - 2 * p)
          ∣ (ρ' - ((ηt : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * μ ^ p) := by
  classical
  haveI : Fact p.Prime := hpri
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  obtain ⟨D, i₀, hi₀mem, hD1, hD2⟩ :=
    exists_second_factor_ideals S hp hπρc hρcop h𝔭B₀ hρ0 hprod
  -- the bound 2m−2p+1 ≥ 2
  have hub : p * (p - 1) ≤ 2 * S.m := by
    have h4 : 2 ∣ p - 1 := by
      have hodd := hpri.out.odd_of_ne_two (by omega)
      rw [Nat.odd_iff] at hodd
      omega
    have h6 : 2 ∣ p * (p - 1) := Dvd.dvd.mul_left h4 p
    have h7 := S.hm
    omega
  have hp5 : 5 ≤ p := by
    by_contra h
    push Not at h
    have hp4 : p = 4 := by omega
    have h2 := hpri.out
    rw [hp4] at h2
    exact absurd h2 (by decide)
  have hbig : 2 ≤ 2 * S.m - 2 * p + 1 := by
    have h1 : 2 * p + 2 ≤ p * (p - 1) := by
      have h2 : p * 4 ≤ p * (p - 1) :=
        Nat.mul_le_mul_left p (by omega)
      have h3 : 2 * p + 2 ≤ 4 * p := by omega
      omega
    omega
  -- conjugation is an involution
  have hinv : ∀ x : 𝓞 (CyclotomicField p ℚ),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        (ringOfIntegersComplexConj (CyclotomicField p ℚ) x) = x := by
    intro x
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    rw [show (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ))
        (ringOfIntegersComplexConj (CyclotomicField p ℚ)
          (ringOfIntegersComplexConj (CyclotomicField p ℚ) x))
        = complexConj (CyclotomicField p ℚ)
          ((algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ))
            (ringOfIntegersComplexConj (CyclotomicField p ℚ) x)) from
      coe_ringOfIntegersComplexConj _ _]
    rw [show (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ))
        (ringOfIntegersComplexConj (CyclotomicField p ℚ) x)
        = complexConj (CyclotomicField p ℚ)
          ((algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)) x) from
      coe_ringOfIntegersComplexConj _ _]
    rw [IsCMField.complexConj_apply_apply]
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  set 𝔭 : Ideal (𝓞 (CyclotomicField p ℚ)) := Ideal.span {(1 - hζ.toInteger)} with h𝔭
  have h𝔭ne0 : 𝔭 ≠ 0 := by
    rw [h𝔭, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hπprime.ne_zero
  have h𝔭prime : Prime 𝔭 :=
    Ideal.prime_of_isPrime (by simpa [h𝔭, Ideal.span_singleton_eq_bot]
      using hπprime.ne_zero)
      ((Ideal.span_singleton_prime hπprime.ne_zero).mpr hπprime)
  -- the deep index is 1
  have h1mem : (1 : 𝓞 (CyclotomicField p ℚ))
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) :=
    Polynomial.one_mem_nthRootsFinset hpri.out.pos
  have hi₀1 : i₀ = 1 := by
    by_contra hne
    have h1 := hD1 1 h1mem
    rw [if_neg (fun h => hne h.symm), pow_one] at h1
    have h2 : (1 - hζ.toInteger) ^ 2
        ∣ (ρ' - ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ') :=
      (pow_dvd_pow _ hbig).trans hdeep
    have h3 : 𝔭 ^ 2
        ∣ Ideal.span {ρ' - 1 * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'} := by
      rw [show ρ' - 1 * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'
          = ρ' - ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ' from by ring,
        h𝔭, Ideal.span_singleton_pow, Ideal.dvd_span_singleton,
        Ideal.mem_span_singleton]
      exact h2
    rw [h1] at h3
    have h4 : 𝔭 ∣ D 1 ^ p := by
      have h5 : 𝔭 * 𝔭 ∣ 𝔭 * D 1 ^ p := by
        rw [← sq]
        exact h3
      exact (mul_dvd_mul_iff_left h𝔭ne0).mp h5
    exact hD2 1 h1mem (h𝔭prime.dvd_of_dvd_pow h4)
  -- the ζ-factor
  have hζmem : hζ.toInteger ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos]
    exact hpow
  have hζne1 : hζ.toInteger ≠ 1 := fun h =>
    (hζ.toInteger_isPrimitiveRoot.ne_one (by omega)) h
  have hζfac := hD1 hζ.toInteger hζmem
  rw [if_neg (hi₀1 ▸ hζne1), pow_one] at hζfac
  -- the τ-quotient: (1−ζ)·τ = ρ' − ζ·ρ̄'
  have hπfac : (1 - hζ.toInteger)
      ∣ (ρ' - hζ.toInteger * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ') := by
    have h1 : 𝔭 ∣ Ideal.span
        {ρ' - hζ.toInteger * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'} := by
      rw [hζfac]
      exact Dvd.intro _ rfl
    rwa [h𝔭, Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at h1
  obtain ⟨τ, hτ⟩ := hπfac
  -- the factor is nonzero
  have hfacne : ρ' - hζ.toInteger * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'
      ≠ 0 := by
    intro h0
    have h1 : Ideal.span {ρ' - hζ.toInteger
        * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'}
        = (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
      rw [h0, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rw [hζfac] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h𝔭ne0 h2
    · have h3 : D hζ.toInteger = 0 := by
        rcases pow_eq_zero_iff (by omega : p ≠ 0) |>.mp h2 with h
        exact h
      exact hD2 hζ.toInteger hζmem (h3 ▸ dvd_zero 𝔭)
  have hτne : τ ≠ 0 := by
    intro h0
    exact hfacne (by rw [hτ, h0, mul_zero])
  -- conjugation of the factor: conj(ρ'−ζρ̄') = −ζ^{p−1}·(ρ'−ζρ̄')
  have hconjfac : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      (ρ' - hζ.toInteger * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ')
      = -hζ.toInteger ^ (p - 1)
        * (ρ' - hζ.toInteger * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ') := by
    rw [map_sub, map_mul, conjO_toInteger hζ, hinv]
    have hzp : hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 := by
      rw [← pow_succ, show p - 1 + 1 = p from by omega, hpow]
    linear_combination (-(ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ')) * hzp
  -- D_ζ is conj-fixed
  set cO : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ) :=
    (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) with hcO
  have hsp2 : 𝔭.map cO = 𝔭 := by
    rw [h𝔭, Ideal.map_span, Set.image_singleton]
    have h2 : cO (1 - hζ.toInteger) = 1 - hζ.toInteger ^ (p - 1) := by
      rw [hcO]
      change ringOfIntegersComplexConj (CyclotomicField p ℚ) (1 - hζ.toInteger) = _
      rw [map_sub, map_one, conjO_toInteger hζ]
    rw [h2]
    refine Ideal.span_singleton_eq_span_singleton.mpr ?_
    exact (one_sub_pow_associated hζ (by omega) (by
      intro hdvd
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))).symm
  have hDfix : (D hζ.toInteger).map cO = D hζ.toInteger := by
    have h1 := congrArg (Ideal.map cO) hζfac
    rw [Ideal.map_mul, Ideal.map_pow, hsp2] at h1
    have hsp1 : (Ideal.span {ρ' - hζ.toInteger
        * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'}).map cO
        = Ideal.span {ρ' - hζ.toInteger
          * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'} := by
      rw [Ideal.map_span, Set.image_singleton]
      refine Ideal.span_singleton_eq_span_singleton.mpr ?_
      rw [show cO (ρ' - hζ.toInteger * ringOfIntegersComplexConj (CyclotomicField p ℚ)
          ρ') = ringOfIntegersComplexConj (CyclotomicField p ℚ)
          (ρ' - hζ.toInteger * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ')
        from rfl, hconjfac]
      refine Associated.symm ?_
      refine associated_unit_mul_right _ _ ?_
      refine IsUnit.neg ?_
      rw [show (hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
          = ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        from rfl]
      exact (hζ.unit'.isUnit).pow _
    rw [hsp1, hζfac] at h1
    have h6 : ((D hζ.toInteger).map cO) ^ p = (D hζ.toInteger) ^ p := by
      exact mul_left_cancel₀ h𝔭ne0 h1.symm
    exact pow_left_injective hpri.out.ne_zero h6
  -- τ is real
  have hπK : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ≠ 0 := hπprime.ne_zero
  have hτreal : ringOfIntegersComplexConj (CyclotomicField p ℚ) τ = τ := by
    have h1 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hτ
    rw [hconjfac, map_mul, show ringOfIntegersComplexConj (CyclotomicField p ℚ)
        (1 - hζ.toInteger) = 1 - hζ.toInteger ^ (p - 1) from by
      rw [map_sub, map_one, conjO_toInteger hζ], hτ] at h1
    -- −ζ^{p−1}(1−ζ)τ = (1−ζ^{p−1})·conj τ; and 1−ζ^{p−1} = −ζ^{p−1}(1−ζ)
    have h2 : (1 - hζ.toInteger ^ (p - 1) : 𝓞 (CyclotomicField p ℚ))
        = -hζ.toInteger ^ (p - 1) * (1 - hζ.toInteger) := by
      have hzp : hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 := by
        rw [← pow_succ, show p - 1 + 1 = p from by omega, hpow]
      linear_combination -hzp
    rw [h2] at h1
    have hune : (-hζ.toInteger ^ (p - 1) * (1 - hζ.toInteger)
        : 𝓞 (CyclotomicField p ℚ)) ≠ 0 := by
      refine mul_ne_zero ?_ hπK
      refine neg_ne_zero.mpr (pow_ne_zero _ ?_)
      exact hζ.toInteger_isPrimitiveRoot.ne_zero (by omega)
    have h3 : (-hζ.toInteger ^ (p - 1) * (1 - hζ.toInteger))
        * ringOfIntegersComplexConj (CyclotomicField p ℚ) τ
        = (-hζ.toInteger ^ (p - 1) * (1 - hζ.toInteger)) * τ := by
      linear_combination -h1
    exact mul_left_cancel₀ hune h3
  -- span{τ} = D_ζ^p
  have hτspan : Ideal.span {τ} = (D hζ.toInteger) ^ p := by
    have h1 : 𝔭 * Ideal.span {τ} = 𝔭 * (D hζ.toInteger) ^ p := by
      rw [h𝔭, Ideal.span_singleton_mul_span_singleton, ← hτ, ← h𝔭, hζfac]
    exact mul_left_cancel₀ h𝔭ne0 h1
  -- the Vandiver engine
  obtain ⟨μ, hμreal, hDspan⟩ := real_principal_of_conjFixed_of_pow_real hζ
    (by omega : 2 < p) hvand hDfix (hD2 _ hζmem) hτreal hτne hτspan
  -- τ = μ^p·ηt with ηt a real unit
  have hassoc : Associated (μ ^ p) τ := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_pow,
      ← hDspan, ← hτspan]
  obtain ⟨ηt, hηt⟩ := hassoc
  have hμpne : μ ^ p ≠ 0 := by
    intro h0
    exact hτne (by rw [← hηt, h0, zero_mul])
  have hηtreal : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      ((ηt : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = ((ηt : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
    have h5 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hηt
    rw [map_mul, map_pow, hμreal, hτreal] at h5
    rw [← hηt] at h5
    exact mul_left_cancel₀ hμpne h5
  -- the final congruence: ρ' − ηt·μ^p = −ζ·(deep)/(1−ζ)
  refine ⟨ηt, μ, hηtreal, hμreal, ?_⟩
  obtain ⟨t, ht⟩ := hdeep
  have hsplit : ρ' - ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ'
      = (1 - hζ.toInteger) * ((1 - hζ.toInteger) ^ (2 * S.m - 2 * p) * t) := by
    rw [ht, ← mul_assoc, ← pow_succ']
  -- (1−ζ)·ρ' = (1−ζ)τ − ζ·(1−ζ)·κ
  have hkey : (1 - hζ.toInteger) * ρ'
      = (1 - hζ.toInteger) * (τ - hζ.toInteger
          * ((1 - hζ.toInteger) ^ (2 * S.m - 2 * p) * t)) := by
    have h6 : (1 - hζ.toInteger) * ρ'
        = (ρ' - hζ.toInteger * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ')
          - hζ.toInteger * (ρ' - ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ')
        := by ring
    rw [h6, hτ, hsplit]
    ring
  have h7 := mul_left_cancel₀ hπK hkey
  rw [show ρ' - ((ηt : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * μ ^ p
      = ρ' - τ + (τ - ((ηt : (𝓞 (CyclotomicField p ℚ))ˣ)
        : 𝓞 (CyclotomicField p ℚ)) * μ ^ p) from by ring]
  have h8 : τ - ((ηt : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * μ ^ p
      = 0 := by
    rw [← hηt]
    ring
  rw [h8, add_zero, h7]
  rw [show τ - hζ.toInteger * ((1 - hζ.toInteger) ^ (2 * S.m - 2 * p) * t) - τ
      = -(hζ.toInteger * ((1 - hζ.toInteger) ^ (2 * S.m - 2 * p) * t)) from by ring]
  exact (Dvd.dvd.mul_left (Dvd.intro t rfl) _).neg_right

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **The two-index elimination** (Washington p. 174): multiplying the step-3 pairs and
subtracting the squared step 1 at indices `a` and `b`,
`λ_aλ_b·(η_a²(ρ_aρ̄_a)^p − η_b²(ρ_bρ̄_b)^p) = (λ_b − λ_a)·(ω+θ)²`. -/
theorem two_index_elimination {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 2 < p) {a b : ℕ}
    (_ha : a.Coprime p) (_hb : b.Coprime p)
    {ηa ηb : (𝓞 (CyclotomicField p ℚ))ˣ} {ρa ρb : 𝓞 (CyclotomicField p ℚ)}
    (heqa : S.ω + hζ.toInteger ^ a * S.θ
      = (1 - hζ.toInteger ^ a)
        * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρa ^ p)
    (heqma : S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ
      = (1 - hζ.toInteger ^ (a * (p - 1)))
        * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p)
    (heqb : S.ω + hζ.toInteger ^ b * S.θ
      = (1 - hζ.toInteger ^ b)
        * ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρb ^ p)
    (heqmb : S.ω + hζ.toInteger ^ (b * (p - 1)) * S.θ
      = (1 - hζ.toInteger ^ (b * (p - 1)))
        * ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb) ^ p) :
    ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1))))
      * ((1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1))))
      * (((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
            * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p
          - ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
            * (ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb) ^ p)
      = (((1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1))))
          - ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))))
        * (S.ω + S.θ) ^ 2 := by
  -- ζ^a·ζ^{a(p−1)} = 1 and ζ^b·ζ^{b(p−1)} = 1
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hzza : hζ.toInteger ^ a * hζ.toInteger ^ (a * (p - 1)) = 1 := by
    rw [← pow_add, show a + a * (p - 1) = a * p from by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega]
      ring, mul_comm, pow_mul, hpow, one_pow]
  have hzzb : hζ.toInteger ^ b * hζ.toInteger ^ (b * (p - 1)) = 1 := by
    rw [← pow_add, show b + b * (p - 1) = b * p from by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega]
      ring, mul_comm, pow_mul, hpow, one_pow]
  -- N_a·D_a = λ_a·η_a²·(ρ_aρ̄_a)^p (and likewise at b), then eliminate ωθ
  have hNa : (S.ω + hζ.toInteger ^ a * S.θ)
        * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)
      = ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1))))
        * (((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
          * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p) := by
    rw [heqa, heqma, mul_pow]
    ring
  have hNb : (S.ω + hζ.toInteger ^ b * S.θ)
        * (S.ω + hζ.toInteger ^ (b * (p - 1)) * S.θ)
      = ((1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1))))
        * (((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
          * (ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb) ^ p) := by
    rw [heqb, heqmb, mul_pow]
    ring
  -- the clean s-form intermediates
  have hNDa : (S.ω + hζ.toInteger ^ a * S.θ)
        * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)
      = S.ω ^ 2 + (hζ.toInteger ^ a + hζ.toInteger ^ (a * (p - 1))) * (S.ω * S.θ)
        + S.θ ^ 2 := by
    linear_combination (S.θ ^ 2) * hzza
  have hNDb : (S.ω + hζ.toInteger ^ b * S.θ)
        * (S.ω + hζ.toInteger ^ (b * (p - 1)) * S.θ)
      = S.ω ^ 2 + (hζ.toInteger ^ b + hζ.toInteger ^ (b * (p - 1))) * (S.ω * S.θ)
        + S.θ ^ 2 := by
    linear_combination (S.θ ^ 2) * hzzb
  have hlama : (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
      = 2 - (hζ.toInteger ^ a + hζ.toInteger ^ (a * (p - 1))) := by
    linear_combination hzza
  have hlamb : (1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1)))
      = 2 - (hζ.toInteger ^ b + hζ.toInteger ^ (b * (p - 1))) := by
    linear_combination hzzb
  -- assemble: pure ring in the s-atoms
  set sa : 𝓞 (CyclotomicField p ℚ)
    := hζ.toInteger ^ a + hζ.toInteger ^ (a * (p - 1)) with hsa
  set sb : 𝓞 (CyclotomicField p ℚ)
    := hζ.toInteger ^ b + hζ.toInteger ^ (b * (p - 1)) with hsb
  rw [hlama] at hNa
  rw [hlamb] at hNb
  rw [hlama, hlamb]
  linear_combination
    (-((2 : 𝓞 (CyclotomicField p ℚ)) - sb)) * hNa
    + ((2 : 𝓞 (CyclotomicField p ℚ)) - sa) * hNb
    + ((2 : 𝓞 (CyclotomicField p ℚ)) - sb) * hNDa
    - ((2 : 𝓞 (CyclotomicField p ℚ)) - sa) * hNDb

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] [IsCMField (CyclotomicField p ℚ)] in
/-- The `λ`-difference factors as a product of two root-differences:
`λ_b − λ_a = (ζ^a − ζ^b)(1 − ζ^{−(a+b)})`. -/
theorem lambda_diff_factorization {ζ : CyclotomicField p ℚ}
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p) (a b : ℕ) :
    (1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1)))
      - (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
    = (hζ.toInteger ^ a - hζ.toInteger ^ b)
      * (1 - hζ.toInteger ^ ((a + b) * (p - 1))) := by
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  -- the two cross-product reductions
  have hred1 : hζ.toInteger ^ a * hζ.toInteger ^ ((a + b) * (p - 1))
      = hζ.toInteger ^ (b * (p - 1)) := by
    rw [← pow_add]
    refine toInteger_pow_eq_of_mod hζ ?_
    have h2 := hpri.out.two_le
    have h3 : a + (a + b) * (p - 1) = a * p + b * (p - 1) := by
      zify [show 1 ≤ p from by omega]
      ring
    rw [h3, show a * p + b * (p - 1) = b * (p - 1) + a * p from by ring,
      Nat.add_mul_mod_self_right]
  have hred2 : hζ.toInteger ^ b * hζ.toInteger ^ ((a + b) * (p - 1))
      = hζ.toInteger ^ (a * (p - 1)) := by
    rw [← pow_add]
    refine toInteger_pow_eq_of_mod hζ ?_
    have h2 := hpri.out.two_le
    have h3 : b + (a + b) * (p - 1) = b * p + a * (p - 1) := by
      zify [show 1 ≤ p from by omega]
      ring
    rw [h3, show b * p + a * (p - 1) = a * (p - 1) + b * p from by ring,
      Nat.add_mul_mod_self_right]
  -- also ζ^xζ^{x(p−1)} = 1 for the λ-expansions
  have hzza : hζ.toInteger ^ a * hζ.toInteger ^ (a * (p - 1)) = 1 := by
    rw [← pow_add, show a + a * (p - 1) = a * p from by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega]
      ring, mul_comm, pow_mul, hpow, one_pow]
  have hzzb : hζ.toInteger ^ b * hζ.toInteger ^ (b * (p - 1)) = 1 := by
    rw [← pow_add, show b + b * (p - 1) = b * p from by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega]
      ring, mul_comm, pow_mul, hpow, one_pow]
  have key : (hζ.toInteger ^ a - hζ.toInteger ^ b)
      * (1 - hζ.toInteger ^ ((a + b) * (p - 1)))
      = hζ.toInteger ^ a - hζ.toInteger ^ (b * (p - 1))
        - hζ.toInteger ^ b + hζ.toInteger ^ (a * (p - 1)) := by
    linear_combination -hred1 + hred2
  have key2 : (1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1)))
      - (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
      = hζ.toInteger ^ a + hζ.toInteger ^ (a * (p - 1))
        - hζ.toInteger ^ b - hζ.toInteger ^ (b * (p - 1)) := by
    linear_combination hzzb - hzza
  linear_combination key2 - key

end FltVandiver.Descent92
