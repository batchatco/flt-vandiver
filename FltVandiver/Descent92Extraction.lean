import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import CyclotomicNT.CaseII
import FltVandiver.Descent92Situation
open CyclotomicNT

/-!
# Descent92, file 2 of 9 — the factor decompositions

Washington pp. 168–169: from the level equation `ω^p + θ^p = η·λ^m·ξ^p`,

* the product factorization `∏_{ζ'^p = 1} (ω + ζ'·θ) = η·λ^m·ξ^p`;
* `(1−ζ)` divides every factor, and `(1−ζ)²` divides only the `ζ' = 1` factor
  (the conjugation argument: a deep factor at `ζ^a ≠ 1` would force a second deep
  factor at `ζ^{−a}`);
* the ideal decompositions `(ω + ζ^aθ) = (1−ζ)·B_a^p` (`a ≢ 0`) and
  `(ω + θ) = (λ)^{m−(p−1)/2}·B₀^p`, with `B_a` pairwise coprime, `(ξ) = ∏B_a`,
  `(1−ζ) ∤ B_a`, and `B_{−a} = conj B_a`. -/

namespace FltVandiver.Descent92

open scoped NumberField
open NumberField NumberField.IsCMField Polynomial
open scoped nonZeroDivisors

variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  [NumberField.IsCMField (CyclotomicField p ℚ)]

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **The product factorization** (Washington p. 168): `∏_{ζ'^p = 1}(ω + ζ'θ) = η·λ^m·ξ^p`. -/
theorem prod_factorization {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) :
    ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), (S.ω + ζ' * S.θ)
      = ((S.η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ S.m * S.ξ ^ p := by
  rw [← S.heq]
  exact (hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul S.ω S.θ
    (hpri.out.odd_of_ne_two (by omega))).symm

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] [IsCMField (CyclotomicField p ℚ)] in
/-- Every `p`-th root of unity is `≡ 1` mod `(1−ζ𝓞)`. -/
theorem pi_dvd_root_sub_one {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {ζ' : 𝓞 (CyclotomicField p ℚ)}
    (hζ' : ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))) :
    (1 - hζ.toInteger) ∣ (ζ' - 1) := by
  by_cases h1 : ζ' = (1 : 𝓞 (CyclotomicField p ℚ))
  · rw [h1, sub_self]
    exact dvd_zero _
  · have hassoc :=
      hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr hζ')
      (Finset.mem_coe.mpr (Polynomial.one_mem_nthRootsFinset hpri.out.pos)) h1
    have h2 : (1 - hζ.toInteger) ∣ (hζ.toInteger - 1) := ⟨-1, by ring⟩
    exact h2.trans hassoc.dvd

/-- `(1−ζ𝓞)` divides `ω + θ` (it divides the product, every factor is congruent to
`ω + θ`). -/
theorem pi_dvd_omega_add_theta {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) :
    (1 - hζ.toInteger) ∣ (S.ω + S.θ) := by
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  -- π divides the right side of the factorization
  have hm1 : 1 ≤ S.m := by
    refine le_trans ?_ S.hm
    have h4 : 2 ≤ p - 1 := by omega
    have h3 : 2 ≤ p * (p - 1) := le_trans h4 (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hdvd : (1 - hζ.toInteger)
      ∣ ((S.η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ S.m * S.ξ ^ p := by
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
    refine dvd_pow ?_ (by omega)
    exact Dvd.intro _ rfl
  rw [← prod_factorization S hp] at hdvd
  obtain ⟨ζ', hζ'mem, hζ'dvd⟩ := hπprime.exists_mem_finset_dvd hdvd
  have h2 : S.ω + S.θ = (S.ω + ζ' * S.θ) - (ζ' - 1) * S.θ := by ring
  rw [h2]
  exact dvd_sub hζ'dvd ((pi_dvd_root_sub_one hζ hζ'mem).mul_right _)

/-- `(1−ζ𝓞)` divides every factor `ω + ζ'θ`. -/
theorem pi_dvd_factor {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) {ζ' : 𝓞 (CyclotomicField p ℚ)}
    (hζ' : ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))) :
    (1 - hζ.toInteger) ∣ (S.ω + ζ' * S.θ) := by
  have h2 : S.ω + ζ' * S.θ = (S.ω + S.θ) + (ζ' - 1) * S.θ := by ring
  rw [h2]
  exact dvd_add (pi_dvd_omega_add_theta S hp)
    ((pi_dvd_root_sub_one hζ hζ').mul_right _)

/-- **Deep-factor uniqueness** (the conjugation argument, Washington p. 168): for
`ζ' ≠ 1` a `p`-th root of unity, `(1−ζ𝓞)²` does not divide `ω + ζ'θ`. -/
theorem pi_sq_not_dvd_factor {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) {ζ' : 𝓞 (CyclotomicField p ℚ)}
    (hζ'mem : ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)))
    (hζ'1 : ζ' ≠ 1) :
    ¬ (1 - hζ.toInteger) ^ 2 ∣ (S.ω + ζ' * S.θ) := by
  intro hdvd
  classical
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) hζ.toInteger
        = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  -- represent ζ' as a power of ζ𝓞
  obtain ⟨k, hk, rfl⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one
    ((Polynomial.mem_nthRootsFinset hpri.out.pos 1).1 hζ'mem)
  have hk0 : ¬ p ∣ k := by
    intro hpk
    apply hζ'1
    obtain ⟨c, hc⟩ := hpk
    rw [hc, pow_mul, hpow, one_pow]
  -- conjugate the divisibility
  obtain ⟨t, ht⟩ := hdvd
  have hconj2 : (1 - hζ.toInteger ^ (p - 1)) ^ 2
      ∣ (S.ω + (hζ.toInteger ^ (p - 1)) ^ k * S.θ) := by
    refine ⟨ringOfIntegersComplexConj (CyclotomicField p ℚ) t, ?_⟩
    have h2 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) ht
    simp only [map_add, map_mul, map_pow, map_sub, map_one, conjO_toInteger hζ,
      S.hω_real, S.hθ_real] at h2
    exact h2
  -- (1 − ζ^{p−1}) is an associate of π
  have hppow_mem : hζ.toInteger ^ (p - 1)
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul, hpow,
      one_pow]
  have hppow_ne : hζ.toInteger ^ (p - 1) ≠ 1 := fun h =>
    (hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by omega)) h
  have hassoc1 : Associated (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
      (1 - hζ.toInteger ^ (p - 1)) := by
    have h2 : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
        (hζ.toInteger ^ (p - 1) - 1) :=
      hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        hpri.out (Finset.mem_coe.mpr hppow_mem)
        (Finset.mem_coe.mpr (Polynomial.one_mem_nthRootsFinset hpri.out.pos)) hppow_ne
    have h3 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) = -(hζ.toInteger - 1) := by
      ring
    have h4 : (1 - hζ.toInteger ^ (p - 1) : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger ^ (p - 1) - 1) := by ring
    rw [h3, h4]
    exact Associated.neg_neg h2
  have hconj3 : (1 - hζ.toInteger) ^ 2
      ∣ (S.ω + (hζ.toInteger ^ (p - 1)) ^ k * S.θ) :=
    ((Associated.pow_pow hassoc1).dvd).trans hconj2
  -- π² divides the difference (ζ^k − ζ^{(p−1)k})·θ
  have hdiff : (1 - hζ.toInteger) ^ 2
      ∣ (hζ.toInteger ^ k - (hζ.toInteger ^ (p - 1)) ^ k) * S.θ := by
    have h3 : (hζ.toInteger ^ k - (hζ.toInteger ^ (p - 1)) ^ k) * S.θ
        = (S.ω + hζ.toInteger ^ k * S.θ)
          - (S.ω + (hζ.toInteger ^ (p - 1)) ^ k * S.θ) := by ring
    rw [h3]
    exact dvd_sub ⟨t, ht⟩ hconj3
  -- but the two roots are distinct, so their difference is a π-associate
  have hne : hζ.toInteger ^ k ≠ (hζ.toInteger ^ (p - 1)) ^ k := by
    intro heq
    rw [← pow_mul] at heq
    have h1 : hζ.toInteger ^ ((p - 1) * k - k) = 1 := by
      have h2 : (p - 1) * k = k + ((p - 1) * k - k) := by
        have := Nat.le_mul_of_pos_left k (show 0 < p - 1 by omega)
        omega
      rw [h2, pow_add] at heq
      have hz0 : hζ.toInteger ^ k ≠ 0 :=
        pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.ne_zero (by omega))
      have heq2 : hζ.toInteger ^ k * 1
          = hζ.toInteger ^ k * hζ.toInteger ^ ((p - 1) * k - k) := by
        rw [mul_one]
        exact heq
      exact (mul_left_cancel₀ hz0 heq2).symm
    have h3 := (hζ.toInteger_isPrimitiveRoot.pow_eq_one_iff_dvd _).mp h1
    have h4 : (p - 1) * k - k = (p - 2) * k := by
      have h5 := hpri.out.two_le
      zify [show 1 ≤ p from by omega, show 2 ≤ p from h5,
        show k ≤ (p - 1) * k from Nat.le_mul_of_pos_left k (by omega)]
      ring
    rw [h4] at h3
    rcases (Nat.Prime.dvd_mul hpri.out).mp h3 with h | h
    · rcases (by omega : 0 < p - 2 ∨ p - 2 = 0) with h6 | h6
      · exact absurd (Nat.le_of_dvd h6 h) (by omega)
      · omega
    · exact hk0 h
  -- the difference of distinct roots is a π-associate
  have hkmem : hζ.toInteger ^ k
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul, hpow,
      one_pow]
  have hkpmem : (hζ.toInteger ^ (p - 1)) ^ k
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, ← pow_mul,
      show (p - 1) * (k * p) = p * ((p - 1) * k) from by ring, pow_mul, hpow, one_pow]
  have hassoc2 : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
      (hζ.toInteger ^ k - (hζ.toInteger ^ (p - 1)) ^ k) :=
    hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr hkmem) (Finset.mem_coe.mpr hkpmem) hne
  obtain ⟨v, hv⟩ := hassoc2
  -- π² ∣ π-associate·θ ⟹ π ∣ θ: contradiction
  have hπne : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ≠ 0 := hπprime.ne_zero
  have h7 : (hζ.toInteger ^ k - (hζ.toInteger ^ (p - 1)) ^ k) * S.θ
      = -((1 - hζ.toInteger) * (((v : (𝓞 (CyclotomicField p ℚ))ˣ)
          : 𝓞 (CyclotomicField p ℚ)) * S.θ)) := by
    rw [← hv]
    ring
  rw [h7, dvd_neg, sq] at hdiff
  have h8 := (mul_dvd_mul_iff_left hπne).mp hdiff
  rcases hπprime.dvd_mul.mp h8 with h9 | h9
  · exact hπprime.not_unit (isUnit_of_dvd_unit h9 v.isUnit)
  · exact S.hlamθ h9

/-! ### The ideal layer -/

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **The span-level factorization**: `∏ (ω + ζ'θ) = 𝔭^{2m}·(ξ)^p` as ideals,
`𝔭 = (1−ζ)`. -/
theorem span_prod_factorization {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) :
    ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      Ideal.span {S.ω + ζ' * S.θ}
    = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m)
      * (Ideal.span {S.ξ}) ^ p := by
  rw [Submodule.prod_span_singleton, prod_factorization S hp]
  have hzu : IsUnit (-hζ.toInteger ^ (p - 1) : 𝓞 (CyclotomicField p ℚ)) := by
    refine IsUnit.neg ?_
    rw [show (hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) from rfl]
    exact (hζ.unit'.isUnit).pow _
  have hassoc : Associated
      ((1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ^ (2 * S.m) * S.ξ ^ p)
      (((S.η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ S.m * S.ξ ^ p) := by
    have h1 : (lambda0 hζ) ^ S.m
        = (-hζ.toInteger ^ (p - 1)) ^ S.m
          * (1 - hζ.toInteger) ^ (2 * S.m) := by
      rw [lambda0_eq_unit_mul_sq hζ hp, mul_pow, ← pow_mul, mul_comm 2 S.m]
    rw [h1]
    have h2 : ((S.η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * ((-hζ.toInteger ^ (p - 1)) ^ S.m * (1 - hζ.toInteger) ^ (2 * S.m)) * S.ξ ^ p
        = (((S.η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * (-hζ.toInteger ^ (p - 1)) ^ S.m)
          * ((1 - hζ.toInteger) ^ (2 * S.m) * S.ξ ^ p) := by ring
    rw [h2]
    exact associated_unit_mul_right _ _ ((S.η.isUnit).mul (hzu.pow _))
  rw [show ((𝓞 (CyclotomicField p ℚ))
      ∙ (((S.η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ S.m * S.ξ ^ p))
      = Ideal.span {((S.η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ S.m * S.ξ ^ p} from rfl]
  rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc,
    ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow]

omit hpri [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] [IsCMField (CyclotomicField p ℚ)] in
/-- Cancellation of prime powers against coprime cofactors (in the ideal monoid). -/
theorem prime_pow_mul_cancel {q X Y : Ideal (𝓞 (CyclotomicField p ℚ))} (hq : Prime q)
    {a b : ℕ} (hX : ¬ q ∣ X) (hY : ¬ q ∣ Y) (h : q ^ a * X = q ^ b * Y) :
    a = b ∧ X = Y := by
  have ha : a = b := by
    rcases Nat.le_total a b with hab | hab
    · by_contra hne
      have h2 : q ^ a * X = q ^ a * (q ^ (b - a) * Y) := by
        rw [h, ← mul_assoc, ← pow_add]
        congr 2
        omega
      have h3 : X = q ^ (b - a) * Y :=
        mul_left_cancel₀ (pow_ne_zero _ hq.ne_zero) h2
      exact hX (h3 ▸ ((dvd_pow_self q (by omega : b - a ≠ 0)).mul_right Y))
    · by_contra hne
      have h2 : q ^ b * Y = q ^ b * (q ^ (a - b) * X) := by
        rw [← h, ← mul_assoc, ← pow_add]
        congr 2
        omega
      have h3 : Y = q ^ (a - b) * X :=
        mul_left_cancel₀ (pow_ne_zero _ hq.ne_zero) h2
      exact hY (h3 ▸ ((dvd_pow_self q (by omega : a - b ≠ 0)).mul_right X))
  subst ha
  exact ⟨rfl, mul_left_cancel₀ (pow_ne_zero _ hq.ne_zero) h⟩

open scoped Classical in
/-- **The factor-ideal decomposition** (Washington pp. 168–169): pairwise coprime ideals
`B_{ζ'}`, prime to `𝔭 = (1−ζ)`, with `(ω + ζ'θ) = 𝔭·B_{ζ'}^p` for `ζ' ≠ 1` and
`(ω + θ) = 𝔭^{2m−(p−1)}·B₁^p`. -/
theorem exists_factor_ideals {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) :
    ∃ B : 𝓞 (CyclotomicField p ℚ) → Ideal (𝓞 (CyclotomicField p ℚ)),
      (∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        Ideal.span {S.ω + ζ' * S.θ}
          = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))})
              ^ (if ζ' = 1 then 2 * S.m - (p - 1) else 1) * (B ζ') ^ p)
      ∧ (∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
          ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ B ζ')
      ∧ (∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), (B ζ')
          = Ideal.span {S.ξ})
      ∧ (∀ ζ₁ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
          ∀ ζ₂ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), ζ₁ ≠ ζ₂ →
          IsCoprime (B ζ₁) (B ζ₂)) := by
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
  -- the dvd-transfer between elements and span-powers
  have hspan_dvd : ∀ (e : ℕ) (x : 𝓞 (CyclotomicField p ℚ)),
      𝔭 ^ e ∣ Ideal.span {x} ↔ (1 - hζ.toInteger) ^ e ∣ x := by
    intro e x
    rw [Ideal.dvd_span_singleton, h𝔭, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  -- nontriviality of the factors
  have hfac_ne : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      S.ω + ζ' * S.θ ≠ 0 := by
    intro ζ' hζ'mem h0
    have h1 : ∏ ζ'' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        (S.ω + ζ'' * S.θ) = 0 :=
      Finset.prod_eq_zero hζ'mem h0
    rw [prod_factorization S hp] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact (S.η.ne_zero) h3
      · exact pow_ne_zero _ (lambda0_ne_zero hζ hp) h3
    · exact S.hξ0 (pow_eq_zero_iff (by omega : p ≠ 0) |>.mp h2)
  -- per-root strip
  have hstrip : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      ∃ (e : ℕ) (C : Ideal (𝓞 (CyclotomicField p ℚ))),
        Ideal.span {S.ω + ζ' * S.θ} = 𝔭 ^ e * C ∧ ¬ 𝔭 ∣ C ∧ (ζ' ≠ 1 → e = 1) := by
    intro ζ' hζ'mem
    by_cases h1 : ζ' = 1
    · -- multiplicity extraction at the deep factor
      have hne : Ideal.span {S.ω + ζ' * S.θ} ≠ 0 := by
        rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
        exact hfac_ne ζ' hζ'mem
      have hfin : FiniteMultiplicity 𝔭 (Ideal.span {S.ω + ζ' * S.θ}) :=
        FiniteMultiplicity.of_prime_left h𝔭prime hne
      obtain ⟨C, hC1, hC2⟩ := hfin.exists_eq_pow_mul_and_not_dvd
      exact ⟨_, C, hC1, hC2, fun h => absurd h1 h⟩
    · -- exactly one π
      obtain ⟨C, hC⟩ : 𝔭 ^ 1 ∣ Ideal.span {S.ω + ζ' * S.θ} :=
        (hspan_dvd 1 _).mpr (by
          rw [pow_one]
          exact pi_dvd_factor S hp hζ'mem)
      refine ⟨1, C, hC, ?_, fun _ => rfl⟩
      intro hdvd
      obtain ⟨D, hD⟩ := hdvd
      have h2 : 𝔭 ^ 2 ∣ Ideal.span {S.ω + ζ' * S.θ} :=
        ⟨D, by rw [hC, hD, pow_one, sq]; ring⟩
      exact pi_sq_not_dvd_factor S hp hζ'mem h1 ((hspan_dvd 2 _).mp h2)
  choose! e C hC1 hC2 hC3 using hstrip
  -- product the strips and cancel the 𝔭-powers
  have hprodC : 𝔭 ^ (∑ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), e ζ')
      * (∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), C ζ')
      = 𝔭 ^ (2 * S.m) * (Ideal.span {S.ξ}) ^ p := by
    rw [← span_prod_factorization S hp,
      Finset.prod_congr rfl (fun ζ' h => hC1 ζ' h), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  have h𝔭C : ¬ 𝔭 ∣ ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), C ζ' := by
    intro hdvd
    obtain ⟨ζ', hζ'mem, hdvd'⟩ := h𝔭prime.exists_mem_finset_dvd hdvd
    exact hC2 ζ' hζ'mem hdvd'
  have h𝔭ξ : ¬ 𝔭 ∣ (Ideal.span {S.ξ}) ^ p := by
    intro hdvd
    have h1 := h𝔭prime.dvd_of_dvd_pow hdvd
    rw [Ideal.dvd_span_singleton, h𝔭, Ideal.mem_span_singleton] at h1
    exact S.hlamξ h1
  obtain ⟨hsum, hCprod⟩ := prime_pow_mul_cancel h𝔭prime h𝔭C h𝔭ξ hprodC
  -- the exponent count: e(1) = 2m − (p−1)
  have hcard := hζ.toInteger_isPrimitiveRoot.card_nthRootsFinset
  have h1mem : (1 : 𝓞 (CyclotomicField p ℚ))
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) :=
    Polynomial.one_mem_nthRootsFinset hpri.out.pos
  have hsum2 : ∑ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), e ζ'
      = e 1 + (p - 1) := by
    rw [← Finset.add_sum_erase _ _ h1mem]
    congr 1
    rw [Finset.sum_congr rfl (fun ζ' h => hC3 ζ' (Finset.mem_of_mem_erase h)
      (Finset.ne_of_mem_erase h))]
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem h1mem, hcard]
  have he1 : e 1 = 2 * S.m - (p - 1) := by
    have hm := S.hm
    have h4 : 2 ∣ p - 1 := by
      have hodd := hpri.out.odd_of_ne_two (by omega)
      rw [Nat.odd_iff] at hodd
      omega
    have h5 : p - 1 ≤ 2 * S.m := by
      have h1 : p * (p - 1) / 2 = p * ((p - 1) / 2) := Nat.mul_div_assoc p h4
      have h2 : p - 1 ≤ p * ((p - 1) / 2) := by
        calc p - 1 = 2 * ((p - 1) / 2) := by omega
          _ ≤ p * ((p - 1) / 2) := Nat.mul_le_mul_right _ (by omega)
      omega
    omega
  -- pairwise coprimality of the stripped ideals (Washington's 𝔮-argument)
  have hpair : ∀ a ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      ∀ b ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), a ≠ b →
      IsCoprime (C a) (C b) := by
    intro a ha b hb hab
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hsup
    obtain ⟨𝔮, h𝔮max, h𝔮⟩ := Ideal.exists_le_maximal _ hsup
    have hCa : C a ≤ 𝔮 := le_trans le_sup_left h𝔮
    have hCb : C b ≤ 𝔮 := le_trans le_sup_right h𝔮
    have hfa : S.ω + a * S.θ ∈ 𝔮 := by
      have h1 : Ideal.span {S.ω + a * S.θ} ≤ C a := by
        rw [hC1 a ha]
        exact Ideal.mul_le_left
      exact hCa (h1 (Ideal.mem_span_singleton_self _))
    have hfb : S.ω + b * S.θ ∈ 𝔮 := by
      have h1 : Ideal.span {S.ω + b * S.θ} ≤ C b := by
        rw [hC1 b hb]
        exact Ideal.mul_le_left
      exact hCb (h1 (Ideal.mem_span_singleton_self _))
    have hdiff : (a - b) * S.θ ∈ 𝔮 := by
      have h2 : (a - b) * S.θ = (S.ω + a * S.θ) - (S.ω + b * S.θ) := by ring
      rw [h2]
      exact sub_mem hfa hfb
    rcases h𝔮max.isPrime.mem_or_mem hdiff with h2 | h2
    · -- a − b ∈ 𝔮 forces 𝔮 = 𝔭, contradicting 𝔭 ∤ C a
      have hassoc : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ)) (a - b) :=
        hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          hpri.out (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
      have hπ𝔮 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔮 := by
        obtain ⟨u, hu⟩ := hassoc
        have h3 : (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
            = (a - b) * ((u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            := by
          rw [← hu, mul_assoc, show ((u : (𝓞 (CyclotomicField p ℚ))ˣ)
              : 𝓞 (CyclotomicField p ℚ))
              * ((u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1 from
            by rw [← Units.val_mul, mul_inv_cancel, Units.val_one], mul_one]
        rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
            = -(hζ.toInteger - 1) from by ring, h3]
        exact neg_mem (Ideal.mul_mem_right _ _ h2)
      have h𝔭le : 𝔭 ≤ 𝔮 := by
        rw [h𝔭, Ideal.span_le]
        simpa using hπ𝔮
      have h𝔭max : 𝔭.IsMaximal :=
        Ideal.IsPrime.isMaximal
          ((Ideal.span_singleton_prime hπprime.ne_zero).mpr hπprime)
          (by simpa [h𝔭, Ideal.span_singleton_eq_bot] using hπprime.ne_zero)
      have h𝔮eq : 𝔮 = 𝔭 := (h𝔭max.eq_of_le h𝔮max.ne_top h𝔭le).symm
      exact hC2 a ha ((Ideal.dvd_iff_le).mpr (h𝔮eq ▸ hCa))
    · -- θ ∈ 𝔮 forces ω ∈ 𝔮, contradicting coprimality
      have hω𝔮 : S.ω ∈ 𝔮 := by
        have h3 : S.ω = (S.ω + a * S.θ) - a * S.θ := by ring
        rw [h3]
        exact sub_mem hfa (Ideal.mul_mem_left _ _ h2)
      have h4 : (⊤ : Ideal (𝓞 (CyclotomicField p ℚ))) ≤ 𝔮 := by
        rw [← Ideal.isCoprime_iff_sup_eq.mp S.hωθ]
        refine sup_le ?_ ?_ <;> rw [Ideal.span_le]
        · simpa using hω𝔮
        · simpa using h2
      exact h𝔮max.ne_top (top_le_iff.mp h4)
  -- extract the p-th powers
  have hex := Finset.exists_eq_pow_of_mul_eq_pow_of_coprime hpair hCprod
  choose! B hB using hex
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro ζ' hζ'mem
    rw [hC1 ζ' hζ'mem, hB ζ' hζ'mem]
    congr 1
    by_cases h1 : ζ' = 1
    · rw [if_pos h1, ← he1, h1]
    · rw [if_neg h1, hC3 ζ' hζ'mem h1]
  · intro ζ' hζ'mem hdvd
    have h1 : 𝔭 ∣ C ζ' := by
      rw [hB ζ' hζ'mem]
      exact hdvd.trans (dvd_pow_self _ (by omega : p ≠ 0))
    exact hC2 ζ' hζ'mem h1
  · -- the p-th-root of ∏B^p = (ξ)^p
    have h1 : (∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), B ζ') ^ p
        = (Ideal.span {S.ξ}) ^ p := by
      rw [← Finset.prod_pow, ← Finset.prod_congr rfl (fun ζ' h => hB ζ' h)]
      exact hCprod
    refine dvd_antisymm ?_ ?_
    · exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by omega : p ≠ 0)).mp
        (h1 ▸ dvd_rfl)
    · exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (by omega : p ≠ 0)).mp
        (h1 ▸ dvd_rfl)
  · -- pairwise coprimality descends from the C's to the B's
    intro ζ₁ h₁ ζ₂ h₂ hne
    have hcop := hpair ζ₁ h₁ ζ₂ h₂ hne
    rw [hB ζ₁ h₁, hB ζ₂ h₂] at hcop
    rw [Ideal.isCoprime_iff_sup_eq] at hcop ⊢
    by_contra hsup
    obtain ⟨𝔮, h𝔮max, h𝔮⟩ := Ideal.exists_le_maximal _ hsup
    have hq1 : B ζ₁ ^ p ≤ 𝔮 :=
      le_trans (Ideal.pow_le_self (by omega)) (le_trans le_sup_left h𝔮)
    have hq2 : B ζ₂ ^ p ≤ 𝔮 :=
      le_trans (Ideal.pow_le_self (by omega)) (le_trans le_sup_right h𝔮)
    exact h𝔮max.ne_top (top_le_iff.mp (hcop ▸ sup_le hq1 hq2))

/-! ### Step 1: the deep factor has a real generator decomposition -/

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- The deep quotient `ρ = (ω+θ)/λ^{m'}` exists, is real, and generates `B₁^p`
(`m' = m − (p−1)/2`). -/
theorem exists_real_quotient {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) {B₁ : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hB₁ : Ideal.span {S.ω + S.θ}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - (p - 1))
        * B₁ ^ p) :
    ∃ ρ : 𝓞 (CyclotomicField p ℚ),
      (lambda0 hζ) ^ (S.m - (p - 1) / 2) * ρ = S.ω + S.θ
      ∧ ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ = ρ
      ∧ Ideal.span {ρ} = B₁ ^ p := by
  have h4 : 2 ∣ p - 1 := by
    have hodd := hpri.out.odd_of_ne_two (by omega)
    rw [Nat.odd_iff] at hodd
    omega
  have hexp : 2 * (S.m - (p - 1) / 2) = 2 * S.m - (p - 1) := by omega
  -- span{λ^{m'}} = 𝔭^{2m'}
  have hspanlam : Ideal.span {(lambda0 hζ) ^ (S.m - (p - 1) / 2)}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))})
        ^ (2 * S.m - (p - 1)) := by
    have h1 : Associated ((lambda0 hζ) ^ (S.m - (p - 1) / 2))
        ((1 - hζ.toInteger) ^ (2 * S.m - (p - 1))) := by
      rw [← hexp, pow_mul]
      refine Associated.pow_pow (show Associated (lambda0 hζ)
          ((1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ^ 2) from ?_)
      rw [lambda0_eq_unit_mul_sq hζ hp]
      refine Associated.symm ?_
      refine associated_unit_mul_right _ _ ?_
      refine IsUnit.neg ?_
      rw [show (hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
          = ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) from rfl]
      exact (hζ.unit'.isUnit).pow _
    rw [Ideal.span_singleton_eq_span_singleton.mpr h1, Ideal.span_singleton_pow]
  -- the divisibility and the quotient
  have hdvd : (lambda0 hζ) ^ (S.m - (p - 1) / 2) ∣ (S.ω + S.θ) := by
    have h1 : Ideal.span {(lambda0 hζ) ^ (S.m - (p - 1) / 2)}
        ∣ Ideal.span {S.ω + S.θ} := by
      rw [hspanlam, hB₁]
      exact Dvd.intro _ rfl
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at h1
  obtain ⟨ρ, hρ⟩ := hdvd
  have hlamne : (lambda0 hζ) ^ (S.m - (p - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (lambda0_ne_zero hζ hp)
  refine ⟨ρ, hρ.symm, ?_, ?_⟩
  · -- realness by cancellation
    have h2 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hρ
    rw [map_add, S.hω_real, S.hθ_real, map_mul, map_pow, conjO_lambda0 hζ] at h2
    rw [hρ] at h2
    exact (mul_left_cancel₀ hlamne h2.symm)
  · -- span{ρ} = B₁^p by ideal cancellation
    have h3 : Ideal.span {(lambda0 hζ) ^ (S.m - (p - 1) / 2)} * Ideal.span {ρ}
        = Ideal.span {(lambda0 hζ) ^ (S.m - (p - 1) / 2)} * B₁ ^ p := by
      rw [Ideal.span_singleton_mul_span_singleton, ← hρ, hB₁, hspanlam]
    have hspanne : Ideal.span {(lambda0 hζ) ^ (S.m - (p - 1) / 2)}
        ≠ (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hlamne
    exact mul_left_cancel₀ hspanne h3

/-- `B₁` is fixed by conjugation (conjugate the decomposition; p-th-root injectivity). -/
theorem deep_ideal_conjFixed {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) {B₁ : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hB₁ : Ideal.span {S.ω + S.θ}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - (p - 1))
        * B₁ ^ p) :
    B₁.map (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = B₁ := by
  set c : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ) :=
    (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) with hc
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  have hcω : c S.ω = S.ω := S.hω_real
  have hcθ : c S.θ = S.θ := S.hθ_real
  have hcζ : c hζ.toInteger = hζ.toInteger ^ (p - 1) := conjO_toInteger hζ
  -- conjugate the decomposition
  have h1 := congrArg (Ideal.map c) hB₁
  rw [Ideal.map_mul, Ideal.map_pow, Ideal.map_pow] at h1
  -- conj of the relevant spans
  have hsp1 : (Ideal.span {S.ω + S.θ}).map c = Ideal.span {S.ω + S.θ} := by
    rw [Ideal.map_span]
    congr 1
    rw [Set.image_singleton, map_add, hcω, hcθ]
  have hsp2 : (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}).map c
      = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} := by
    rw [Ideal.map_span, Set.image_singleton]
    have h2 : c (1 - hζ.toInteger) = 1 - hζ.toInteger ^ (p - 1) := by
      rw [map_sub, map_one, hcζ]
    rw [h2]
    refine Ideal.span_singleton_eq_span_singleton.mpr ?_
    -- 1 − ζ^{p−1} ~ 1 − ζ (the pairwise-associated fact, with sign flips)
    have hpow : hζ.toInteger ^ p = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
        (CyclotomicField p ℚ)
      have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          hζ.toInteger = ζ := hζ.coe_toInteger
      rw [map_pow, map_one, ht]
      exact hζ.pow_eq_one
    have hmem : hζ.toInteger ^ (p - 1)
        ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
      rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
        hpow, one_pow]
    have hne1 : hζ.toInteger ^ (p - 1) ≠ 1 := fun h =>
      (hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by omega)) h
    have h3 : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
        (hζ.toInteger ^ (p - 1) - 1) :=
      hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        hpri.out (Finset.mem_coe.mpr hmem)
        (Finset.mem_coe.mpr (Polynomial.one_mem_nthRootsFinset hpri.out.pos)) hne1
    have h4 : (1 - hζ.toInteger ^ (p - 1) : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger ^ (p - 1) - 1) := by ring
    have h5 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) := by ring
    rw [h4, h5]
    exact (Associated.neg_neg h3).symm
  rw [hsp1, hsp2] at h1
  -- cancel the 𝔭-power, then the p-th root
  have h𝔭ne : (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))})
      ^ (2 * S.m - (p - 1)) ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hπprime.ne_zero
  have h6 : (B₁.map c) ^ p = B₁ ^ p := mul_left_cancel₀ h𝔭ne (by rw [← hB₁, ← h1])
  exact pow_left_injective hpri.out.ne_zero h6

omit [IsCMField (CyclotomicField p ℚ)] in
/-- An ideal prime to `𝔭` is coprime to `(p)`. -/
theorem deep_ideal_coprime_p {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (_hp : 2 < p) {B₁ : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hB₁ne : ¬ Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ∣ B₁) :
    IsCoprime B₁ (Ideal.span {((p : ℕ) : 𝓞 (CyclotomicField p ℚ))}) := by
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  obtain ⟨𝔮, h𝔮max, h𝔮⟩ := Ideal.exists_le_maximal _ hsup
  have hB : B₁ ≤ 𝔮 := le_trans le_sup_left h𝔮
  have hpmem : ((p : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔮 :=
    (le_trans le_sup_right h𝔮) (Ideal.mem_span_singleton_self _)
  -- p = unit·(1−ζ)^{p−1} ⟹ 1−ζ ∈ 𝔮
  obtain ⟨u, hu⟩ := associated_zeta_sub_one_pow_prime hζ
  have hπ𝔮 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔮 := by
    have h2 : ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) - 1
        ∈ 𝔮 := by
      have h3 : (((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          - 1) ^ (p - 1)
          = ((p : ℕ) : 𝓞 (CyclotomicField p ℚ))
            * ((u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
        rw [← hu, mul_assoc, show ((u : (𝓞 (CyclotomicField p ℚ))ˣ)
            : 𝓞 (CyclotomicField p ℚ))
            * ((u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) = 1 from
          by rw [← Units.val_mul, mul_inv_cancel, Units.val_one], mul_one]
        simp only [IsPrimitiveRoot.coe_unit']
      have h4 : (((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          - 1) ^ (p - 1) ∈ 𝔮 := by
        rw [h3]
        exact Ideal.mul_mem_right _ _ hpmem
      exact (h𝔮max.isPrime.mem_of_pow_mem _ h4)
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -((((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))) - 1)
      from by
      rw [show ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          = hζ.toInteger from rfl]
      ring]
    exact neg_mem h2
  -- so 𝔮 = 𝔭 divides B₁: contradiction
  have h𝔭max : (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}).IsMaximal :=
    Ideal.IsPrime.isMaximal
      ((Ideal.span_singleton_prime hπprime.ne_zero).mpr hπprime)
      (by simpa [Ideal.span_singleton_eq_bot] using hπprime.ne_zero)
  have h𝔭le : Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ≤ 𝔮 := by
    rw [Ideal.span_le]
    simpa using hπ𝔮
  have h𝔮eq : 𝔮 = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} :=
    (h𝔭max.eq_of_le h𝔮max.ne_top h𝔭le).symm
  exact hB₁ne ((Ideal.dvd_iff_le).mpr (h𝔮eq ▸ hB))

/-- **Washington step 1**: under Vandiver, `ω + θ = η₀·λ^{m'}·ρ₀^p` with `η₀` a real unit
and `ρ₀` real (`m' = m − (p−1)/2`). -/
theorem step1_real_decomposition {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 2 < p) (hvand : IsVandiverPrime p) :
    ∃ (η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) (ρ₀ : 𝓞 (CyclotomicField p ℚ)),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = ((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      ∧ ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ₀ = ρ₀
      ∧ S.ω + S.θ = ((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * (lambda0 hζ) ^ (S.m - (p - 1) / 2) * ρ₀ ^ p := by
  classical
  -- the B₁-decomposition
  obtain ⟨B, hB1, hB2, _, _⟩ := exists_factor_ideals S hp
  have h1mem : (1 : 𝓞 (CyclotomicField p ℚ))
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) :=
    Polynomial.one_mem_nthRootsFinset hpri.out.pos
  have hB₁ : Ideal.span {S.ω + S.θ}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - (p - 1))
        * (B 1) ^ p := by
    have h1 := hB1 1 h1mem
    rwa [if_pos rfl, one_mul] at h1
  -- the real quotient
  obtain ⟨ρ, hρeq, hρreal, hρspan⟩ := exists_real_quotient S hp hB₁
  -- B₁ descends
  have hfix := deep_ideal_conjFixed S hp hB₁
  have hcop := deep_ideal_coprime_p (hζ := hζ) hp (hB2 1 h1mem)
  obtain ⟨A, hA⟩ := isExtended_of_conjFixed_of_coprime hp hfix (by
    convert hcop using 2)
  -- ρ is the image of a real-subfield element
  have hρ_range : ρ ∈ Set.range (algebraMap (𝓞 (MaximalRealCyclotomic p))
      (𝓞 (CyclotomicField p ℚ))) := by
    rw [← NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff]
    exact hρreal
  obtain ⟨ρplus, hρplus⟩ := hρ_range
  -- A^p = (ρ⁺) in the real subring (map-injectivity by faithful flatness)
  have hApmap : (A ^ p).map (algebraMap (𝓞 (MaximalRealCyclotomic p))
        (𝓞 (CyclotomicField p ℚ)))
      = (Ideal.span {ρplus}).map (algebraMap (𝓞 (MaximalRealCyclotomic p))
        (𝓞 (CyclotomicField p ℚ))) := by
    rw [Ideal.map_pow, ← hA, ← hρspan, Ideal.map_span, Set.image_singleton, hρplus]
  haveI hff : Module.FaithfullyFlat (𝓞 (MaximalRealCyclotomic p))
      (𝓞 (CyclotomicField p ℚ)) := inferInstance
  have hAp : A ^ p = Ideal.span {ρplus} := by
    have h2 := congrArg (Ideal.comap (algebraMap (𝓞 (MaximalRealCyclotomic p))
      (𝓞 (CyclotomicField p ℚ)))) hApmap
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat,
      Ideal.comap_map_eq_self_of_faithfullyFlat] at h2
  -- nontriviality
  have hρ0 : ρ ≠ 0 := by
    intro h0
    have h1 : S.ω + S.θ = 0 := by rw [← hρeq, h0, mul_zero]
    have h2 : ∏ ζ'' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        (S.ω + ζ'' * S.θ) = 0 :=
      Finset.prod_eq_zero h1mem (by rw [one_mul]; exact h1)
    rw [prod_factorization S hp] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact S.η.ne_zero h4
      · exact pow_ne_zero _ (lambda0_ne_zero hζ hp) h4
    · exact S.hξ0 (pow_eq_zero_iff (by omega : p ≠ 0) |>.mp h3)
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, Ideal.zero_eq_bot, Ideal.map_bot] at hA
    apply hρ0
    rw [← Ideal.span_singleton_eq_bot, hρspan, hA, ← Ideal.zero_eq_bot,
      zero_pow (by omega : p ≠ 0)]
  -- Vandiver kills the class of A
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
  set ρ₀ : 𝓞 (CyclotomicField p ℚ) :=
    algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ)) ρ0plus with hρ₀
  have hB₁span : B 1 = Ideal.span {ρ₀} := by
    rw [hA, hρ0plus, Ideal.map_span, Set.image_singleton]
  have hρ₀real : ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ₀ = ρ₀ := by
    rw [NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff]
    exact ⟨ρ0plus, rfl⟩
  -- the unit between ρ and ρ₀^p
  have hassoc : Associated (ρ₀ ^ p) ρ := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_pow,
      ← hB₁span, ← hρspan]
  obtain ⟨u, hu⟩ := hassoc
  have hρ₀ne : ρ₀ ^ p ≠ 0 := by
    intro h0
    exact hρ0 (by rw [← hu, h0, zero_mul])
  refine ⟨u, ρ₀, ?_, hρ₀real, ?_⟩
  · -- the unit is real: conjugate ρ₀^p·u = ρ and cancel
    have h5 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hu
    rw [map_mul, map_pow, hρ₀real, hρreal] at h5
    rw [← hu] at h5
    exact mul_left_cancel₀ hρ₀ne h5
  · -- assemble: ω + θ = λ^{m'}·ρ = u·λ^{m'}·ρ₀^p
    rw [← hρeq, ← hu]
    ring

end FltVandiver.Descent92
