import FltVandiver.Descent92Second
import FltVandiver.Descent
open CyclotomicNT

/-!
# Descent92, file 6 of 9 — the iteration

Washington p. 172: from Assumption II (now the theorem `assumption_II`), the next
descent level is

  `ω₁ = w·ρ_aρ̄_a`, `θ₁ = −ρ_bρ̄_b`, `ξ₁ = ρ₀²`, `m₁ = 2m − p`,

(with `w` the real-adjusted `p`-th root of `(η_a/η_b)²`), satisfying
`ω₁^p + θ₁^p = η₁·λ^{m₁}·ξ₁^p` — a new `Situation92` with the measure
`#distinct primes of ξ` strictly decreased (unless in the minimal case).
-/

namespace FltVandiver.Descent92

open scoped NumberField nonZeroDivisors
open NumberField NumberField.IsCMField Polynomial

variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  [NumberField.IsCMField (CyclotomicField p ℚ)]

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **The real-witness adjustment**: a unit whose `p`-th power is conjugation-fixed can
be replaced by a REAL unit with the same `p`-th power (the `(p+1)/2`-trick). -/
theorem real_adjust (hp : 2 < p) {w : (𝓞 (CyclotomicField p ℚ))ˣ}
    (hreal : ringOfIntegersComplexConj (CyclotomicField p ℚ)
        (((w ^ p : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
      = (((w ^ p : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))) :
    ∃ w' : (𝓞 (CyclotomicField p ℚ))ˣ,
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((w' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = ((w' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      ∧ w' ^ p = w ^ p := by
  classical
  set cM : (𝓞 (CyclotomicField p ℚ)) →* (𝓞 (CyclotomicField p ℚ)) :=
    (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)).toMonoidHom with hcM
  set u : (𝓞 (CyclotomicField p ℚ))ˣ := Units.map cM w * w⁻¹ with hu
  have huval : ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = ringOfIntegersComplexConj (CyclotomicField p ℚ)
          ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((w⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
    rw [hu, Units.val_mul]
    rfl
  -- u^p = 1
  have hup : u ^ p = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, huval, mul_pow, Units.val_one]
    have h1 : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))) ^ p
        = ringOfIntegersComplexConj (CyclotomicField p ℚ)
          (((w ^ p : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)) := by
      rw [← map_pow, Units.val_pow_eq_pow_val]
    rw [h1, hreal, Units.val_pow_eq_pow_val]
    have h2 : ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ p
        * ((w⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ p = 1 := by
      rw [← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow]
    exact h2
  -- σ(w-val) = u-val·w-val
  have hσw : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
    rw [huval, mul_assoc, show ((w⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)
        : 𝓞 (CyclotomicField p ℚ))
        * ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1 from by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one], mul_one]
  -- the (p+1)/2-trick at the value level
  have hupval : (((u : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)) ^ p
      = 1 := by
    rw [← Units.val_pow_eq_pow_val, hup, Units.val_one]
  have hw0 : ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ≠ 0 :=
    Units.ne_zero w
  have hreal' := CaseIIVandiverDescent.exists_real_assoc (p := p)
    (by omega : p ≠ 2) hw0 hupval hσw
  refine ⟨u ^ ((p + 1) / 2) * w, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_pow_eq_pow_val]
    exact hreal'
  · rw [mul_pow, ← pow_mul, show (p + 1) / 2 * p = p * ((p + 1) / 2) from
      mul_comm _ _, pow_mul, hup, one_pow, one_mul]

set_option maxHeartbeats 1000000 in -- heavy elaboration: exceeds the default heartbeat budget
/-- **The iterated equation** (Washington p. 172): with the real-adjusted Assumption-II
witness `w`, `(w·ρ_aρ̄_a)^p + (−ρ_bρ̄_b)^p = η₁·λ^{2m−p}·(ρ₀²)^p` for a unit `η₁`. -/
theorem iterated_equation {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 3 < p) {a b : ℕ}
    (ha : a.Coprime p) (hb : b.Coprime p) (hpab : ¬ p ∣ (a + b))
    (hneab : hζ.toInteger ^ a ≠ hζ.toInteger ^ b)
    {ηa ηb η₀ w : (𝓞 (CyclotomicField p ℚ))ˣ}
    {ρa ρb ρ₀ : 𝓞 (CyclotomicField p ℚ)}
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
        * (ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb) ^ p)
    (heq0 : S.ω + S.θ
      = ((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ (S.m - (p - 1) / 2) * ρ₀ ^ p)
    (hwp : w ^ p = ηa ^ 2 * (ηb ^ 2)⁻¹) :
    ∃ η₁ : (𝓞 (CyclotomicField p ℚ))ˣ,
      (((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)) ^ p
        + (-(ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb)) ^ p
      = ((η₁ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ (2 * S.m - p) * (ρ₀ ^ 2) ^ p := by
  classical
  have hpa : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hpri.out).mp ha.symm
  have hpb : ¬ p ∣ b := (Nat.Prime.coprime_iff_not_dvd hpri.out).mp hb.symm
  have helim := two_index_elimination S (by omega) ha hb heqa heqma heqb heqmb
  have hfact := lambda_diff_factorization hζ (by omega) a b
  -- the unit witnesses for the π-associates
  obtain ⟨v1, hv1⟩ : Associated (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
      (hζ.toInteger ^ a - hζ.toInteger ^ b) := by
    have hpow : hζ.toInteger ^ p = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
        (CyclotomicField p ℚ)
      have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          hζ.toInteger = ζ := hζ.coe_toInteger
      rw [map_pow, map_one, ht]
      exact hζ.pow_eq_one
    have hamem : hζ.toInteger ^ a
        ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
      rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
        hpow, one_pow]
    have hbmem : hζ.toInteger ^ b
        ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
      rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
        hpow, one_pow]
    have h3 :=
      hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        hpri.out (Finset.mem_coe.mpr hamem) (Finset.mem_coe.mpr hbmem) hneab
    exact Associated.trans ⟨-1, by
      simp only [Units.val_neg, Units.val_one]
      ring⟩ h3
  obtain ⟨v2, hv2⟩ := one_sub_pow_associated hζ (by omega)
    (j := (a + b) * (p - 1)) (by
      intro hdvd
      rcases (Nat.Prime.dvd_mul hpri.out).mp hdvd with h | h
      · exact hpab h
      · exact absurd (Nat.le_of_dvd (by omega) h) (by omega))
  obtain ⟨v3, hv3⟩ : Associated ((1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ^ 2)
      ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))) := by
    rw [sq]
    exact Associated.mul_mul (one_sub_pow_associated hζ (by omega) hpa)
      (one_sub_pow_associated hζ (by omega) (by
        intro hdvd
        rcases (Nat.Prime.dvd_mul hpri.out).mp hdvd with h | h
        · exact hpa h
        · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)))
  obtain ⟨v4, hv4⟩ : Associated ((1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ^ 2)
      ((1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1)))) := by
    rw [sq]
    exact Associated.mul_mul (one_sub_pow_associated hζ (by omega) hpb)
      (one_sub_pow_associated hζ (by omega) (by
        intro hdvd
        rcases (Nat.Prime.dvd_mul hpri.out).mp hdvd with h | h
        · exact hpb h
        · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)))
  -- the substitution chain
  have hp2 : 2 < p := by omega
  have hodd : Odd p := hpri.out.odd_of_ne_two (by omega)
  have hwpv : ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ p
      * ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
      = ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2 := by
    have h1 : w ^ p * ηb ^ 2 = ηa ^ 2 := by
      rw [hwp, mul_assoc, inv_mul_cancel, mul_one]
    have h2 := congrArg (Units.val) h1
    simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using h2
  set X : 𝓞 (CyclotomicField p ℚ) :=
    (((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)) ^ p
      + (-(ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb)) ^ p with hX
  -- (A) ηa²Pa − ηb²Pb = ηb²·X
  have hA : ((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
        * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p
      - ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
        * (ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb) ^ p
      = ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2 * X := by
    rw [hX, mul_pow, Odd.neg_pow hodd]
    linear_combination (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p
      * (-hwpv)
  -- (B) λb − λa = (1−ζ)²·v1·v2
  have hB : ((1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1)))
        - (1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1))))
      = (1 - hζ.toInteger) ^ 2
        * (((v1 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * ((v2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))) := by
    rw [hfact, ← hv1, ← hv2]
    ring
  -- (C) (ω+θ)² = η₀²·Λ^{2m−p+1}·ρ₀^{2p}
  have hC : (S.ω + S.θ) ^ 2
      = ((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
        * (lambda0 hζ) ^ (2 * S.m - p + 1) * ρ₀ ^ (2 * p) := by
    rw [heq0]
    have h4 : 2 ∣ p - 1 := by
      have hodd2 := hpri.out.odd_of_ne_two (by omega)
      rw [Nat.odd_iff] at hodd2
      omega
    have hub : p * (p - 1) ≤ 2 * S.m := by
      have h6 : 2 ∣ p * (p - 1) := Dvd.dvd.mul_left h4 p
      have h7 := S.hm
      omega
    have h8 : (p - 1) / 2 ≤ S.m := by
      refine le_trans ?_ S.hm
      refine Nat.div_le_div_right ?_
      exact Nat.le_mul_of_pos_left _ (by omega)
    have h9 : 2 * ((p - 1) / 2) = p - 1 := by omega
    have h10 : p ≤ p * (p - 1) := Nat.le_mul_of_pos_right p (by omega)
    have hexp : (S.m - (p - 1) / 2) * 2 = 2 * S.m - p + 1 := by omega
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, hexp]
    ring
  -- (D) λaλb = (1−ζ)⁴·v3·v4
  have hD : ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1))))
        * ((1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1))))
      = (1 - hζ.toInteger) ^ 4
        * (((v3 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * ((v4 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))) := by
    rw [← hv3, ← hv4]
    ring
  -- (E) Λ^{2m−p+1} = Λ^{2m−p}·(−ζ^{p−1})·(1−ζ)²
  have hE : (lambda0 hζ) ^ (2 * S.m - p + 1)
      = (lambda0 hζ) ^ (2 * S.m - p)
        * (-hζ.toInteger ^ (p - 1) * (1 - hζ.toInteger) ^ 2) := by
    rw [pow_succ, lambda0_eq_unit_mul_sq hζ hp2]
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  -- the η₁-unit
  refine ⟨v3⁻¹ * v4⁻¹ * (ηb ^ 2)⁻¹ * (v1 * v2) * η₀ ^ 2
    * (-(hζ.unit' ^ (p - 1))), ?_⟩
  -- multiply through by (1−ζ)⁴·v3·v4·ηb² and use the elimination
  have hCne : ((1 - hζ.toInteger) ^ 4
      * (((v3 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((v4 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
      * ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2)
      ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hπprime.ne_zero)
      (mul_ne_zero (Units.ne_zero v3) (Units.ne_zero v4)))
      (pow_ne_zero _ (Units.ne_zero ηb))
  refine mul_left_cancel₀ hCne ?_
  have hval : (((-(hζ.unit' ^ (p - 1)) : (𝓞 (CyclotomicField p ℚ))ˣ))
      : 𝓞 (CyclotomicField p ℚ)) = -hζ.toInteger ^ (p - 1) := by
    simp only [Units.val_neg, Units.val_pow_eq_pow_val]
    rfl
  have huu : ∀ u : (𝓞 (CyclotomicField p ℚ))ˣ,
      ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1 := by
    intro u
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hη2 : ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
      * (((ηb ^ 2)⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1
      := by
    rw [show ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
        = ((ηb ^ 2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) from by
      rw [Units.val_pow_eq_pow_val], ← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc ((1 - hζ.toInteger) ^ 4
        * (((v3 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * ((v4 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
        * ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2) * X
      = ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1))))
          * ((1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1))))
        * (((ηa : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
            * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) ^ p
          - ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
            * (ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb) ^ p) := by
        rw [hD, hA]
        ring
    _ = (((1 - hζ.toInteger ^ b) * (1 - hζ.toInteger ^ (b * (p - 1))))
          - ((1 - hζ.toInteger ^ a) * (1 - hζ.toInteger ^ (a * (p - 1)))))
        * (S.ω + S.θ) ^ 2 := helim
    _ = (1 - hζ.toInteger) ^ 4
        * ((((v1 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * ((v2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
          * (((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
            * ((lambda0 hζ) ^ (2 * S.m - p)
              * (-hζ.toInteger ^ (p - 1)) * ρ₀ ^ (2 * p)))) := by
        rw [hB, hC, hE]
        ring
    _ = _ := by
        set E1 : 𝓞 (CyclotomicField p ℚ) :=
          (((v3⁻¹ * v4⁻¹ * (ηb ^ 2)⁻¹ * (v1 * v2) * η₀ ^ 2
            * (-(hζ.unit' ^ (p - 1))) : (𝓞 (CyclotomicField p ℚ))ˣ))
            : 𝓞 (CyclotomicField p ℚ)) with hE1
        have hcoll : (((v3 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * ((v4 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
            * ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2 * E1
            = ((v1 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * ((v2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * ((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
              * (-hζ.toInteger ^ (p - 1)) := by
          rw [hE1]
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, hval]
          rw [show (((v3 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                * ((v4 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
              * ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
              * (((v3⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                * ((v4⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                * (((ηb ^ 2)⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)
                  : 𝓞 (CyclotomicField p ℚ))
                * (((v1 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                  * ((v2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
                * ((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
                * (-hζ.toInteger ^ (p - 1)))
              = (((v3 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                  * ((v3⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
                * (((v4 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                  * ((v4⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)
                    : 𝓞 (CyclotomicField p ℚ)))
                * (((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
                  * (((ηb ^ 2)⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)
                    : 𝓞 (CyclotomicField p ℚ)))
                * (((v1 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                  * ((v2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                  * ((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
                  * (-hζ.toInteger ^ (p - 1))) from by ring,
            huu v3, huu v4, hη2, one_mul, one_mul, one_mul]
        rw [show (ρ₀ ^ (2 * p) : 𝓞 (CyclotomicField p ℚ)) = (ρ₀ ^ 2) ^ p from by
          rw [← pow_mul]]
        calc (1 - hζ.toInteger) ^ 4
            * ((((v1 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                * ((v2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
              * (((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
                * ((lambda0 hζ) ^ (2 * S.m - p)
                  * (-hζ.toInteger ^ (p - 1)) * (ρ₀ ^ 2) ^ p)))
            = (1 - hζ.toInteger) ^ 4
              * (((((v3 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
                  * ((v4 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
                * ((ηb : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ 2
                * E1)
              * ((lambda0 hζ) ^ (2 * S.m - p) * (ρ₀ ^ 2) ^ p)) := by
              rw [hcoll]
              ring
          _ = _ := by ring

set_option maxHeartbeats 1000000 in -- heavy elaboration: exceeds the default heartbeat budget
/-- **The next descent level**: assemble the iterated data into a new `Situation92` with
`m₁ = 2m − p` and `ξ₁ = ρ₀²`. -/
theorem next_situation {ζ : CyclotomicField p ℚ}
    {hζ : IsPrimitiveRoot ζ p} (S : Situation92 hζ) (hp : 3 < p)
    {w η₁ : (𝓞 (CyclotomicField p ℚ))ˣ} {ρa ρb ρ₀ : 𝓞 (CyclotomicField p ℚ)}
    (hweq : (((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)) ^ p
        + (-(ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb)) ^ p
      = ((η₁ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ (2 * S.m - p) * (ρ₀ ^ 2) ^ p)
    (hwreal : ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)))
    (hρ₀real : ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ₀ = ρ₀)
    (hcab : IsCoprime
      (Ideal.span {ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa})
      (Ideal.span {ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb}))
    (hca0 : IsCoprime
      (Ideal.span {ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa})
      (Ideal.span {ρ₀ ^ 2}))
    (hcb0 : IsCoprime
      (Ideal.span {ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb})
      (Ideal.span {ρ₀ ^ 2}))
    (hπa : ¬ (1 - hζ.toInteger)
      ∣ (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa))
    (hπb : ¬ (1 - hζ.toInteger)
      ∣ (ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb))
    (hπ0 : ¬ (1 - hζ.toInteger) ∣ ρ₀)
    (hρ₀0 : ρ₀ ≠ 0) :
    ∃ S' : Situation92 hζ, S'.m = 2 * S.m - p ∧ S'.ξ = ρ₀ ^ 2 := by
  classical
  -- the involution
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
  have hprodreal : ∀ x : 𝓞 (CyclotomicField p ℚ),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        (x * ringOfIntegersComplexConj (CyclotomicField p ℚ) x)
      = x * ringOfIntegersComplexConj (CyclotomicField p ℚ) x := by
    intro x
    rw [map_mul, hinv]
    ring
  -- the m-arithmetic
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
  have hple : p * 4 ≤ p * (p - 1) := Nat.mul_le_mul_left p (by omega)
  have hm1 : p * (p - 1) / 2 ≤ 2 * S.m - p := by
    have h7 := S.hm
    have h8 : p * (p - 1) / 2 * 2 ≤ p * (p - 1) := Nat.div_mul_le_self _ 2
    omega
  obtain ⟨km, hkm⟩ := S.hm_dvd
  have hkm4 : 4 ≤ km := by
    have h9 : p * 4 ≤ p * km := by omega
    exact Nat.le_of_mul_le_mul_left h9 (by omega)
  have hfexp : p * (2 * km - 2) = 2 * (p * km) - 2 * p := by
    have h10 : p * 1 ≤ p * km := Nat.mul_le_mul_left p (by omega)
    zify [show 2 ≤ 2 * km from by omega, show 2 * p ≤ 2 * (p * km) from by omega]
    ring
  -- π-coprimality of ω₁
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  refine ⟨{
    ω := ((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)
    θ := -(ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb)
    ξ := ρ₀ ^ 2
    η := η₁
    m := 2 * S.m - p
    hm := hm1
    hm_dvd := ⟨2 * km - 2, by omega⟩
    hω_real := by
      rw [map_mul, hwreal, hprodreal]
    hθ_real := by
      rw [map_neg, hprodreal]
    hξ_real := by
      rw [map_pow, hρ₀real]
    hη_real := ?ηreal
    heq := hweq
    hωθ := ?c1
    hωξ := ?c2
    hθξ := ?c3
    hlamω := ?l1
    hlamθ := ?l2
    hlamξ := ?l3
    hξ0 := pow_ne_zero _ hρ₀0 }, rfl, rfl⟩
  case c1 =>
    rw [show Ideal.span {((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)}
        = Ideal.span {ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa} from
      Ideal.span_singleton_eq_span_singleton.mpr
        (Associated.symm (associated_unit_mul_right _ _ w.isUnit))]
    rw [show Ideal.span {-(ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb)}
        = Ideal.span {ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb} from by
      rw [Ideal.span_singleton_neg]]
    exact hcab
  case c2 =>
    rw [show Ideal.span {((w : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa)}
        = Ideal.span {ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa} from
      Ideal.span_singleton_eq_span_singleton.mpr
        (Associated.symm (associated_unit_mul_right _ _ w.isUnit))]
    exact hca0
  case c3 =>
    rw [show Ideal.span {-(ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb)}
        = Ideal.span {ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb} from by
      rw [Ideal.span_singleton_neg]]
    exact hcb0
  case l1 =>
    intro hdvd
    rcases hπprime.dvd_mul.mp hdvd with h | h
    · exact hπprime.not_unit (isUnit_of_dvd_unit h w.isUnit)
    · exact hπa h
  case l2 =>
    intro hdvd
    rw [dvd_neg] at hdvd
    exact hπb hdvd
  case l3 =>
    intro hdvd
    exact hπ0 (hπprime.dvd_of_dvd_pow hdvd)
  case ηreal =>
    -- realness by cancellation against the equation
    have h1 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hweq
    rw [map_add, map_pow, map_pow, map_mul, hwreal, hprodreal, map_neg, hprodreal,
      map_mul, map_mul, map_pow, conjO_lambda0 hζ, map_pow, map_pow, hρ₀real] at h1
    rw [hweq] at h1
    have hne : (lambda0 hζ) ^ (2 * S.m - p) * (ρ₀ ^ 2) ^ p
        ≠ (0 : 𝓞 (CyclotomicField p ℚ)) :=
      mul_ne_zero (pow_ne_zero _ (lambda0_ne_zero hζ (by omega)))
        (pow_ne_zero _ (pow_ne_zero _ hρ₀0))
    have h2 : ((η₁ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((lambda0 hζ) ^ (2 * S.m - p) * (ρ₀ ^ 2) ^ p)
        = ringOfIntegersComplexConj (CyclotomicField p ℚ)
            ((η₁ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * ((lambda0 hζ) ^ (2 * S.m - p) * (ρ₀ ^ 2) ^ p) := by
      linear_combination h1
    exact (mul_right_cancel₀ hne h2).symm

end FltVandiver.Descent92
