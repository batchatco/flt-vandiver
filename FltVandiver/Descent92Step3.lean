import FltVandiver.Descent92Alpha
open CyclotomicNT

/-!
# Descent92, file 4 of 9 — the per-index real decomposition (Washington's step 3)

Washington p. 171: for `a` coprime to `p`,

  `ω + ζ^aθ = (1−ζ^a)·η_a·ρ_a^p`,   `η_a` a REAL unit (`η_a = η_{−a}`),  `ρ̄_a = ρ_{−a}`.

Chain: the conj-swap pair product `σ_a = (ω+ζ^aθ)(ω+ζ^{−a}θ)/λ_a` is real and generates
`(B_aB_{−a})^p`; the pair ideal is conj-FIXED (the swap!) so the step-1 isExtended +
Vandiver pattern gives a real generator `ρ'_a`; combining with step 2's `α = w^p`:
`((ω+ζ^aθ)/(1−ζ^a))² = ε'_a·(ρ'_a w)^p` in `K`; the `(p+1)/2`-power extracts the result
(`β = β^{p+1}/β^p`), with integrality of `ρ_a` from integral closedness. -/

namespace FltVandiver.Descent92

open scoped NumberField nonZeroDivisors
open NumberField NumberField.IsCMField Polynomial
open CaseIIVandiverRouteA

variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  [NumberField.IsCMField (CyclotomicField p ℚ)]

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] [IsCMField (CyclotomicField p ℚ)] in
/-- For `p ∤ j`, `(1 − ζ𝓞^j) ~ (1 − ζ𝓞)`. -/
theorem one_sub_pow_associated {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (_hp : 2 < p) {j : ℕ} (hj : ¬ p ∣ j) :
    Associated (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) (1 - hζ.toInteger ^ j) := by
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hmem : hζ.toInteger ^ j ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
      hpow, one_pow]
  have hne : hζ.toInteger ^ j ≠ 1 := by
    intro h1
    exact hj ((hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd j).mp h1)
  have h3 : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
      (hζ.toInteger ^ j - 1) :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr hmem)
      (Finset.mem_coe.mpr (Polynomial.one_mem_nthRootsFinset hpri.out.pos)) hne
  have h4 : (1 - hζ.toInteger ^ j : 𝓞 (CyclotomicField p ℚ))
      = -(hζ.toInteger ^ j - 1) := by ring
  have h5 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) = -(hζ.toInteger - 1) := by
    ring
  rw [h4, h5]
  exact Associated.neg_neg h3

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] [IsCMField (CyclotomicField p ℚ)] in
/-- Powers of `ζ𝓞` depend only on the exponent mod `p`. -/
theorem toInteger_pow_eq_of_mod {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {m n : ℕ} (h : m % p = n % p) : hζ.toInteger ^ m = hζ.toInteger ^ n := by
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hred : ∀ k : ℕ, hζ.toInteger ^ k = hζ.toInteger ^ (k % p) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k p]
    rw [pow_add, pow_mul, hpow, one_pow, mul_one]
  rw [hred m, hred n, h]

/-- The conj-swap pair quotient `σ_a = (ω+ζ^aθ)(ω+ζ^{−a}θ)/λ_a` exists, is real, and
generates `(B_a·B_{−a})^p`. -/
theorem exists_pair_quotient {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) {a : ℕ} (ha : a.Coprime p)
    {Ba Bma : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hBa : Ideal.span {S.ω + hζ.toInteger ^ a * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Ba ^ p)
    (hBma : Ideal.span {S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Bma ^ p) :
    ∃ σa : 𝓞 (CyclotomicField p ℚ),
      (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1))) * σa
        = (S.ω + hζ.toInteger ^ a * S.θ) * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)
      ∧ ringOfIntegersComplexConj (CyclotomicField p ℚ) σa = σa
      ∧ Ideal.span {σa} = (Ba * Bma) ^ p := by
  classical
  have hpa : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hpri.out).mp ha.symm
  have hpa2 : ¬ p ∣ a * (p - 1) := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hpri.out).mp hdvd with h | h
    · exact hpa h
    · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hassoc1 := one_sub_pow_associated hζ hp hpa
  have hassoc2 := one_sub_pow_associated hζ hp hpa2
  -- span of the pair uniformizer
  have hspanlam : Ideal.span
      {(1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ^ 2 := by
    rw [← Ideal.span_singleton_mul_span_singleton, sq,
      ← Ideal.span_singleton_eq_span_singleton.mpr hassoc1,
      ← Ideal.span_singleton_eq_span_singleton.mpr hassoc2]
  -- the product identity
  have hprod : Ideal.span {(S.ω + hζ.toInteger ^ a * S.θ)
        * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ^ 2
        * (Ba * Bma) ^ p := by
    rw [← Ideal.span_singleton_mul_span_singleton, hBa, hBma, mul_pow, sq]
    ring
  -- divisibility and the quotient
  have hdvd : (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
      ∣ (S.ω + hζ.toInteger ^ a * S.θ) * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ) := by
    have h1 : Ideal.span {(1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))}
        ∣ Ideal.span {(S.ω + hζ.toInteger ^ a * S.θ)
            * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)} := by
      rw [hspanlam, hprod]
      exact Dvd.intro _ rfl
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at h1
  obtain ⟨σa, hσa⟩ := hdvd
  have hlamne : ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))
      : 𝓞 (CyclotomicField p ℚ)) ≠ 0 := by
    have hπne : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ≠ 0 := by
      have h1 := hζ.zeta_sub_one_prime'
      have h2 : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
        rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
            = -(hζ.toInteger - 1) from by ring]
        exact h1.neg
      exact h2.ne_zero
    refine mul_ne_zero (fun h0 => hπne ?_) (fun h0 => hπne ?_)
    · obtain ⟨u, hu⟩ := hassoc1
      rw [← hu] at h0
      exact (mul_eq_zero.mp h0).resolve_right (Units.ne_zero u)
    · obtain ⟨u, hu⟩ := hassoc2
      rw [← hu] at h0
      exact (mul_eq_zero.mp h0).resolve_right (Units.ne_zero u)
  refine ⟨σa, hσa.symm, ?_, ?_⟩
  · -- realness: conj swaps the factors of N·D and fixes λ_a
    have hcN : ringOfIntegersComplexConj (CyclotomicField p ℚ)
        (S.ω + hζ.toInteger ^ a * S.θ)
        = S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ := by
      rw [map_add, map_mul, map_pow, conjO_toInteger hζ, S.hω_real, S.hθ_real,
        ← pow_mul, mul_comm (p - 1) a]
    have hredD : ((p - 1) * (a * (p - 1))) % p = a % p := by
      have h2 := hpri.out.two_le
      have h3 : (p - 1) * (a * (p - 1)) = a * ((p - 1) * (p - 1)) := by ring
      have h4 : (p - 1) * (p - 1) = p * (p - 2) + 1 := by
        zify [show 1 ≤ p from by omega, show 2 ≤ p from h2]
        ring
      rw [h3, h4]
      rw [show a * (p * (p - 2) + 1) = a + (a * (p - 2)) * p from by ring]
      rw [Nat.add_mul_mod_self_right]
    have hcD : ringOfIntegersComplexConj (CyclotomicField p ℚ)
        (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)
        = S.ω + hζ.toInteger ^ a * S.θ := by
      rw [map_add, map_mul, map_pow, conjO_toInteger hζ, S.hω_real, S.hθ_real,
        ← pow_mul, toInteger_pow_eq_of_mod hζ hredD]
    have hcLa : ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1))))
        = (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1))) := by
      simp only [map_mul, map_sub, map_one, map_pow, conjO_toInteger hζ]
      rw [← pow_mul, ← pow_mul, mul_comm (p - 1) a, toInteger_pow_eq_of_mod hζ hredD]
      ring
    have h5 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hσa
    rw [map_mul, map_mul, hcN, hcD, hcLa] at h5
    rw [show (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)
        * (S.ω + hζ.toInteger ^ a * S.θ)
        = (S.ω + hζ.toInteger ^ a * S.θ)
          * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ) from mul_comm _ _] at h5
    rw [hσa] at h5
    exact mul_left_cancel₀ hlamne h5.symm
  · -- the span: cancellation
    have h6 : Ideal.span {(1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))}
          * Ideal.span {σa}
        = Ideal.span {(1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))}
          * (Ba * Bma) ^ p := by
      rw [Ideal.span_singleton_mul_span_singleton, ← hσa, hprod, hspanlam]
    have hspanne : Ideal.span
        {(1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))}
        ≠ (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hlamne
    exact mul_left_cancel₀ hspanne h6

/-- **The Vandiver real-principal engine**: a conj-fixed ideal `B`, prime to `𝔭`, whose
`p`-th power is generated by a real element, is principal with a REAL generator.
(The second half of step 1, reusable for the step-3 pair ideals.) -/
theorem real_principal_of_conjFixed_of_pow_real {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (_hζ' : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hvand : IsVandiverPrime p)
    {B : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hfix : B.map (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = B)
    (hcop : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ B)
    {ρ : 𝓞 (CyclotomicField p ℚ)}
    (hρreal : ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ = ρ) (hρ0 : ρ ≠ 0)
    (hspan : Ideal.span {ρ} = B ^ p) :
    ∃ ρ₀ : 𝓞 (CyclotomicField p ℚ),
      ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ₀ = ρ₀
      ∧ B = Ideal.span {ρ₀} := by
  classical
  obtain ⟨A, hA⟩ := isExtended_of_conjFixed_of_coprime hp hfix (by
    have h1 := deep_ideal_coprime_p (hζ := hζ) hp hcop
    convert h1 using 2)
  have hρ_range : ρ ∈ Set.range (algebraMap (𝓞 (MaximalRealCyclotomic p))
      (𝓞 (CyclotomicField p ℚ))) := by
    rw [← NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff]
    exact hρreal
  obtain ⟨ρplus, hρplus⟩ := hρ_range
  have hApmap : (A ^ p).map (algebraMap (𝓞 (MaximalRealCyclotomic p))
        (𝓞 (CyclotomicField p ℚ)))
      = (Ideal.span {ρplus}).map (algebraMap (𝓞 (MaximalRealCyclotomic p))
        (𝓞 (CyclotomicField p ℚ))) := by
    rw [Ideal.map_pow, ← hA, ← hspan, Ideal.map_span, Set.image_singleton, hρplus]
  have hAp : A ^ p = Ideal.span {ρplus} := by
    have h2 := congrArg (Ideal.comap (algebraMap (𝓞 (MaximalRealCyclotomic p))
      (𝓞 (CyclotomicField p ℚ)))) hApmap
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat,
      Ideal.comap_map_eq_self_of_faithfullyFlat] at h2
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, Ideal.zero_eq_bot, Ideal.map_bot] at hA
    apply hρ0
    rw [← Ideal.span_singleton_eq_bot, hspan, hA, ← Ideal.zero_eq_bot,
      zero_pow (by omega : p ≠ 0)]
  have hAmem : A ∈ (Ideal (𝓞 (MaximalRealCyclotomic p)))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hA0
  have hApmem : A ^ p ∈ (Ideal (𝓞 (MaximalRealCyclotomic p)))⁰ := pow_mem hAmem p
  have hclass : ClassGroup.mk0 ⟨A, hAmem⟩ ^ p = 1 := by
    have hsub : (⟨A, hAmem⟩ : (Ideal (𝓞 (MaximalRealCyclotomic p)))⁰) ^ p
        = ⟨A ^ p, hApmem⟩ := Subtype.ext (by push_cast; ring)
    rw [← map_pow, hsub]
    refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
    rw [hAp]
    exact ⟨⟨ρplus, rfl⟩⟩
  have hA1 := hvand.pow_eq_one_eq_one hclass
  obtain ⟨ρ0plus, hρ0plus⟩ := (ClassGroup.mk0_eq_one_iff hAmem).mp hA1
  refine ⟨algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ)) ρ0plus,
    ?_, ?_⟩
  · rw [NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff]
    exact ⟨ρ0plus, rfl⟩
  · rw [hA, hρ0plus, Ideal.map_span, Set.image_singleton]

/-- Conjugation swaps the pair ideals: `conj(B_a) = B_{−a}`. -/
theorem pair_ideal_conjSwap {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) {a : ℕ}
    {Ba Bma : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hBa : Ideal.span {S.ω + hζ.toInteger ^ a * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Ba ^ p)
    (hBma : Ideal.span {S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Bma ^ p) :
    Ba.map (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = Bma := by
  classical
  set c : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ) :=
    (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) with hc
  have hcω : c S.ω = S.ω := S.hω_real
  have hcθ : c S.θ = S.θ := S.hθ_real
  have hcζ : c hζ.toInteger = hζ.toInteger ^ (p - 1) := conjO_toInteger hζ
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  -- conjugate the a-equation
  have h1 := congrArg (Ideal.map c) hBa
  rw [Ideal.map_mul, Ideal.map_pow] at h1
  have hsp1 : (Ideal.span {S.ω + hζ.toInteger ^ a * S.θ}).map c
      = Ideal.span {S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ} := by
    rw [Ideal.map_span]
    congr 1
    rw [Set.image_singleton, map_add, map_mul, map_pow, hcζ, hcω, hcθ, ← pow_mul,
      mul_comm (p - 1) a]
  have hsp2 : (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}).map c
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} := by
    rw [Ideal.map_span, Set.image_singleton]
    have h2 : c (1 - hζ.toInteger) = 1 - hζ.toInteger ^ (p - 1) := by
      rw [map_sub, map_one, hcζ]
    rw [h2]
    refine Ideal.span_singleton_eq_span_singleton.mpr ?_
    exact (one_sub_pow_associated hζ hp (by
      intro hdvd
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega))).symm
  rw [hsp1, hsp2, hBma] at h1
  have h𝔭ne : Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}
      ≠ (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hπprime.ne_zero
  have h6 : Bma ^ p = (Ba.map c) ^ p := mul_left_cancel₀ h𝔭ne h1
  exact (pow_left_injective hpri.out.ne_zero h6).symm

/-- **Step 3, the pair decomposition**: under Vandiver, the conj-swap pair has
`(ω+ζ^aθ)(ω+ζ^{−a}θ) = ε'_a·λ_a·ρ'^p` with `ε'_a` a real unit and `ρ'` real. -/
theorem step3_pair_real_principal {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) (hvand : IsVandiverPrime p) {a : ℕ}
    (ha : a.Coprime p) {Ba Bma : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hBa : Ideal.span {S.ω + hζ.toInteger ^ a * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Ba ^ p)
    (hBma : Ideal.span {S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Bma ^ p)
    (h𝔭Ba : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ Ba)
    (h𝔭Bma : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ Bma) :
    ∃ (ε' : (𝓞 (CyclotomicField p ℚ))ˣ) (ρ' : 𝓞 (CyclotomicField p ℚ)),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      ∧ ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ' = ρ'
      ∧ (S.ω + hζ.toInteger ^ a * S.θ) * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)
        = ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))) * ρ' ^ p := by
  classical
  obtain ⟨σa, hσeq, hσreal, hσspan⟩ := exists_pair_quotient S hp ha hBa hBma
  -- the pair ideal is conj-fixed
  have hswap1 := pair_ideal_conjSwap S hp hBa hBma
  -- the reverse swap: the a(p−1)-indexed equation conjugates back to the a-equation
  have hredD : ((p - 1) * (a * (p - 1))) % p = a % p := by
    have h2 := hpri.out.two_le
    have h3 : (p - 1) * (a * (p - 1)) = a * ((p - 1) * (p - 1)) := by ring
    have h4 : (p - 1) * (p - 1) = p * (p - 2) + 1 := by
      zify [show 1 ≤ p from by omega, show 2 ≤ p from h2]
      ring
    rw [h3, h4, show a * (p * (p - 2) + 1) = a + (a * (p - 2)) * p from by ring,
      Nat.add_mul_mod_self_right]
  have hBa' : Ideal.span {S.ω + hζ.toInteger ^ (a * (p - 1) * (p - 1)) * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Ba ^ p := by
    rw [show (a * (p - 1) * (p - 1)) = ((p - 1) * (a * (p - 1))) from by ring,
      toInteger_pow_eq_of_mod hζ hredD]
    exact hBa
  have hswap2 := pair_ideal_conjSwap S hp hBma hBa'
  have hfix : (Ba * Bma).map (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = Ba * Bma := by
    rw [Ideal.map_mul, hswap1, hswap2, mul_comm]
  have h𝔭prod : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}
      ∣ Ba * Bma := by
    intro hdvd
    have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
      have h1 := hζ.zeta_sub_one_prime'
      rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
          = -(hζ.toInteger - 1) from by ring]
      exact h1.neg
    have h𝔭prime : Prime (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) :=
      Ideal.prime_of_isPrime (by
        simpa [Ideal.span_singleton_eq_bot] using hπprime.ne_zero)
        ((Ideal.span_singleton_prime hπprime.ne_zero).mpr hπprime)
    rcases h𝔭prime.dvd_mul.mp hdvd with h | h
    · exact h𝔭Ba h
    · exact h𝔭Bma h
  -- σ_a ≠ 0
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
  have hσ0 : σa ≠ 0 := by
    intro h0
    have h1 : (S.ω + hζ.toInteger ^ a * S.θ)
        * (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ) = 0 := by
      rw [← hσeq, h0, mul_zero]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hfacO _ hamem h2
    · exact hfacO _ hamem2 h2
  -- the engine
  obtain ⟨ρ', hρ'real, hρ'span⟩ := real_principal_of_conjFixed_of_pow_real hζ hp hvand
    hfix h𝔭prod hσreal hσ0 hσspan
  -- the unit between σ_a and ρ'^p
  have hassoc : Associated (ρ' ^ p) σa := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_pow,
      ← hρ'span, ← hσspan]
  obtain ⟨ε', hε'⟩ := hassoc
  have hρ'ne : ρ' ^ p ≠ 0 := by
    intro h0
    exact hσ0 (by rw [← hε', h0, zero_mul])
  refine ⟨ε', ρ', ?_, hρ'real, ?_⟩
  · have h5 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hε'
    rw [map_mul, map_pow, hρ'real, hσreal] at h5
    rw [← hε'] at h5
    exact mul_left_cancel₀ hρ'ne h5
  · rw [← hσeq, ← hε']
    ring

/-- K-level square identity: from the pair identity and the α-ratio,
`A² = ε·(1−z)²·(ρ'w)^p`. -/
theorem square_identity {K' : Type*} [Field K'] {A B z ε ρ' w : K'} {q : ℕ}
    (hB : B ≠ 0) (hz : z ≠ 0)
    (hpair : A * B = ε * ((1 - z) * (1 - z⁻¹)) * ρ' ^ q)
    (hratio : w ^ q = -z⁻¹ * A / B) :
    A ^ 2 = ε * (1 - z) ^ 2 * (ρ' * w) ^ q := by
  have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  have hAB : A = B * (-z * w ^ q) := by
    have h0 : w ^ q * B = -z⁻¹ * A := by
      rw [hratio]
      field_simp
    have h1 : z * (w ^ q * B) = z * (-z⁻¹ * A) := congrArg (z * ·) h0
    linear_combination h1 - A * hzz
  have hlam : (1 - z) * (1 - z⁻¹) = -z⁻¹ * (1 - z) ^ 2 := by
    have h0 : z * ((1 - z) * (1 - z⁻¹)) = z * (-z⁻¹ * (1 - z) ^ 2) := by
      linear_combination ((1 - z) ^ 2 - (1 - z)) * hzz
    exact mul_left_cancel₀ hz h0
  have h1 : A ^ 2 * B = (ε * (1 - z) ^ 2 * (ρ' * w) ^ q) * B := by
    calc A ^ 2 * B = A * (A * B) := by ring
      _ = (B * (-z * w ^ q)) * (ε * (-z⁻¹ * (1 - z) ^ 2) * ρ' ^ q) := by
          rw [← hAB, hpair, hlam]
      _ = (ε * (1 - z) ^ 2 * (ρ' * w) ^ q) * B * (z * z⁻¹) := by ring
      _ = (ε * (1 - z) ^ 2 * (ρ' * w) ^ q) * B := by
          rw [mul_inv_cancel₀ hz, mul_one]
  exact mul_right_cancel₀ hB h1

/-- K-level `(q+1)/2`-extraction: from `A² = u·γ^q` (`q` odd), `A = u^{(q+1)/2}·δ^q`
with `δ = γ^{(q+1)/2}/A`. -/
theorem half_power_extraction {K' : Type*} [Field K'] {A u γ : K'} {q : ℕ}
    (hq : Odd q) (hA : A ≠ 0) (hsq : A ^ 2 = u * γ ^ q) :
    A = u ^ ((q + 1) / 2) * (γ ^ ((q + 1) / 2) / A) ^ q := by
  have hq2 : 2 * ((q + 1) / 2) = q + 1 := by
    obtain ⟨k, hk⟩ := hq
    omega
  have h1 : A ^ (q + 1) = u ^ ((q + 1) / 2) * γ ^ (q * ((q + 1) / 2)) := by
    calc A ^ (q + 1) = (A ^ 2) ^ ((q + 1) / 2) := by
          rw [← pow_mul, hq2]
      _ = u ^ ((q + 1) / 2) * γ ^ (q * ((q + 1) / 2)) := by
          rw [hsq, mul_pow, ← pow_mul]
  have h2 : (γ ^ ((q + 1) / 2) / A) ^ q = γ ^ (q * ((q + 1) / 2)) / A ^ q := by
    rw [div_pow, ← pow_mul, mul_comm ((q + 1) / 2) q]
  rw [h2]
  have h3 : u ^ ((q + 1) / 2) * (γ ^ (q * ((q + 1) / 2)) / A ^ q)
      = u ^ ((q + 1) / 2) * γ ^ (q * ((q + 1) / 2)) / A ^ q := by ring
  rw [h3, eq_div_iff (pow_ne_zero _ hA)]
  rw [show A * A ^ q = A ^ (q + 1) from (pow_succ' A q).symm]
  exact h1

/-- **Washington step 3** (one index): under Vandiver,
`ω + ζ^aθ = (1−ζ^a)·η_a·ρ_a^p` with `η_a = ε'_a^{(p+1)/2}` a real unit. -/
theorem step3_single_decomposition {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 2 < p)
    (hvand : IsVandiverPrime p) {a : ℕ} (ha : a.Coprime p)
    {Ba Bma : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hBa : Ideal.span {S.ω + hζ.toInteger ^ a * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Ba ^ p)
    (hBma : Ideal.span {S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Bma ^ p)
    (h𝔭Ba : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ Ba)
    (h𝔭Bma : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ Bma) :
    ∃ (ηa : (𝓞 (CyclotomicField p ℚ))ˣ) (ρa : 𝓞 (CyclotomicField p ℚ)),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      ∧ S.ω + hζ.toInteger ^ a * S.θ
        = (1 - hζ.toInteger ^ a)
          * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρa ^ p := by
  classical
  obtain ⟨ε', ρ', hε'real, hρ'real, hpair⟩ :=
    step3_pair_real_principal S hp hvand ha hBa hBma h𝔭Ba h𝔭Bma
  obtain ⟨w, hw⟩ := step2_alpha_pth_power S hp
    ((Nat.Prime.coprime_iff_not_dvd hpri.out).mp hvand) ha
  have hpa : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hpri.out).mp ha.symm
  set f : 𝓞 (CyclotomicField p ℚ) →+* CyclotomicField p ℚ :=
    (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)) with hf
  have hfinj : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  have ht : f hζ.toInteger = ζ := hζ.coe_toInteger
  -- the 𝓞-quotient β with N = (1−ζ^a)·β
  have hamem : hζ.toInteger ^ a ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    have hpow : hζ.toInteger ^ p = 1 := by
      apply hfinj
      rw [map_pow, map_one, ht]
      exact hζ.pow_eq_one
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
      hpow, one_pow]
  have hβdvd : (1 - hζ.toInteger ^ a) ∣ (S.ω + hζ.toInteger ^ a * S.θ) :=
    ((one_sub_pow_associated hζ hp hpa).symm.dvd).trans (pi_dvd_factor S hp hamem)
  obtain ⟨β, hβ⟩ := hβdvd
  -- K-level data
  set z : CyclotomicField p ℚ := ζ ^ a with hzdef
  have hz0 : z ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
  have hz1 : z ≠ 1 := by
    intro h1
    exact hpa ((hζ.pow_eq_one_iff_dvd a).mp h1)
  have h1z : (1 : CyclotomicField p ℚ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hzainv : z⁻¹ = ζ ^ (a * (p - 1)) := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [hzdef, ← pow_add, show a * (p - 1) + a = a * p from by
      have h2 := hpri.out.two_le
      zify [show 1 ≤ p from by omega]
      ring, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- images
  have hfA : f (S.ω + hζ.toInteger ^ a * S.θ)
      = f S.ω + z * f S.θ := by
    rw [map_add, map_mul, map_pow, ht, hzdef]
  have hfB : f (S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ)
      = f S.ω + z⁻¹ * f S.θ := by
    rw [map_add, map_mul, map_pow, ht, hzainv]
  -- nonvanishing
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
  have hamem2 : hζ.toInteger ^ (a * (p - 1))
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    have hpow : hζ.toInteger ^ p = 1 := by
      apply hfinj
      rw [map_pow, map_one, ht]
      exact hζ.pow_eq_one
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul,
      show a * (p - 1) * p = p * (a * (p - 1)) from by ring, pow_mul, hpow, one_pow]
  have hB0 : f S.ω + z⁻¹ * f S.θ ≠ 0 := by
    rw [← hfB]
    exact fun h0 => hfacO _ hamem2 (hfinj (by rw [h0, map_zero]))
  -- the K-level pair identity
  have hpairK : (f S.ω + z * f S.θ) * (f S.ω + z⁻¹ * f S.θ)
      = f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((1 - z) * (1 - z⁻¹)) * (f ρ') ^ p := by
    have h1 := congrArg f hpair
    rw [map_mul, map_mul, map_mul, map_pow, hfA, hfB] at h1
    rw [h1]
    congr 2
    simp only [map_mul, map_sub, map_one, map_pow, ht]
    rw [hzdef, hzainv]
  -- the ratio from step 2
  have hratioK : w ^ p = -z⁻¹ * (f S.ω + z * f S.θ) / (f S.ω + z⁻¹ * f S.θ) := by
    rw [hw, routeAElt]
  -- the square identity
  have hsq := square_identity hB0 hz0 hpairK hratioK
  -- Ã := f β; Ã·(1−z) = A; cancel the (1−z)²
  have hAβ : f S.ω + z * f S.θ = (1 - z) * f β := by
    rw [← hfA, hβ]
    rw [map_mul, map_sub, map_one, map_pow, ht, hzdef]
  have hβsq : (f β) ^ 2
      = f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (f ρ' * w) ^ p := by
    have h2 : ((1 - z) * f β) ^ 2
        = f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * (1 - z) ^ 2 * (f ρ' * w) ^ p := by
      rw [← hAβ]
      exact hsq
    have h3 : (1 - z) ^ 2 * (f β) ^ 2
        = (1 - z) ^ 2 * (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ)
            : 𝓞 (CyclotomicField p ℚ)) * (f ρ' * w) ^ p) := by
      rw [show (1 - z) ^ 2 * (f β) ^ 2 = ((1 - z) * f β) ^ 2 from by ring, h2]
      ring
    exact mul_left_cancel₀ (pow_ne_zero _ h1z) h3
  -- the (p+1)/2-extraction
  have hβ0 : f β ≠ 0 := by
    intro h0
    apply hfacO _ hamem
    apply hfinj
    rw [map_zero, hfA, hAβ, h0, mul_zero]
  -- the (p+1)/2-extraction
  have hodd : Odd p := hpri.out.odd_of_ne_two (by omega)
  have hext := half_power_extraction hodd hβ0 hβsq
  set ρhat : CyclotomicField p ℚ := (f ρ' * w) ^ ((p + 1) / 2) / f β with hρhatdef
  -- the inverse-unit power and the p-th power of ρhat
  have huu : f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      * f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hρp : ρhat ^ p = f (β * (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ))
      : 𝓞 (CyclotomicField p ℚ)) ^ ((p + 1) / 2)) := by
    rw [map_mul, map_pow]
    have h2 : f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
          ^ ((p + 1) / 2) * f β
        = f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
          ^ ((p + 1) / 2)
          * (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              ^ ((p + 1) / 2) * ρhat ^ p) := by
      rw [← hext]
    rw [show f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
          ^ ((p + 1) / 2)
          * (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              ^ ((p + 1) / 2) * ρhat ^ p)
        = (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)))
            ^ ((p + 1) / 2) * ρhat ^ p from by ring, huu, one_pow, one_mul] at h2
    rw [← h2]
    ring
  -- integrality lift
  obtain ⟨ρa, hρa⟩ : ∃ ρa : 𝓞 (CyclotomicField p ℚ), f ρa = ρhat := by
    have h1 : IsIntegral ℤ (ρhat ^ p) := by
      rw [hρp]
      exact (β * (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ))
        : 𝓞 (CyclotomicField p ℚ)) ^ ((p + 1) / 2)).2
    have h2 : IsIntegral ℤ ρhat := h1.of_pow (by omega)
    exact ⟨⟨ρhat, h2⟩, rfl⟩
  refine ⟨ε' ^ ((p + 1) / 2), ρa, ?_, ?_⟩
  · rw [Units.val_pow_eq_pow_val, map_pow, hε'real]
  · apply hfinj
    rw [hfA, hAβ]
    rw [map_mul, map_mul, map_sub, map_one, map_pow, ht, ← hzdef,
      Units.val_pow_eq_pow_val, map_pow, map_pow, hρa]
    rw [show (1 - z) * f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ)
          : 𝓞 (CyclotomicField p ℚ)) ^ ((p + 1) / 2) * ρhat ^ p
        = (1 - z) * (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ)
            : 𝓞 (CyclotomicField p ℚ)) ^ ((p + 1) / 2) * ρhat ^ p) from by ring]
    rw [← hext]

/-- **Washington step 3, packaged for the pair**: both equations with the SHARED real
unit `η_a`, and `ρ_{−a} := conj(ρ_a)` (making the conjugate-normalization canonical). -/
theorem step3_packaged {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) (hvand : IsVandiverPrime p) {a : ℕ}
    (ha : a.Coprime p)
    {Ba Bma : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hBa : Ideal.span {S.ω + hζ.toInteger ^ a * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Ba ^ p)
    (hBma : Ideal.span {S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ}
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} * Bma ^ p)
    (h𝔭Ba : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ Ba)
    (h𝔭Bma : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ Bma) :
    ∃ (ηa : (𝓞 (CyclotomicField p ℚ))ˣ) (ρa : 𝓞 (CyclotomicField p ℚ)),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      ∧ S.ω + hζ.toInteger ^ a * S.θ
        = (1 - hζ.toInteger ^ a)
          * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρa ^ p
      ∧ S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ
        = (1 - hζ.toInteger ^ (a * (p - 1)))
          * ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p := by
  obtain ⟨ηa, ρa, hηreal, heq⟩ :=
    step3_single_decomposition S hp hvand ha hBa hBma h𝔭Ba h𝔭Bma
  refine ⟨ηa, ρa, hηreal, heq, ?_⟩
  -- conjugate the equation
  have h1 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) heq
  rw [map_add, map_mul, map_pow, conjO_toInteger hζ, S.hω_real, S.hθ_real,
    map_mul, map_mul, map_sub, map_one, map_pow, conjO_toInteger hζ, map_pow,
    hηreal, ← pow_mul, mul_comm (p - 1) a] at h1
  exact h1

end FltVandiver.Descent92
