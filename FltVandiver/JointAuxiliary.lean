import FltVandiver.CaseII95Descent
import FltVandiver.SophieGermain
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# The joint auxiliary: Sophie Germain and Vandiver on one prime, no size bound

The frozen Case II descent (`CaseII95Descent`) consumes the size bound `ℓ < p² − p` only
through Lemmas 9.6 and 9.7. Here Lemma 9.6 is run from the weaker hypothesis `p ∤ (ℓ−1)/p`
(`lemma_9_6_zmod_joint` builds the order-`p²` element directly), and Lemma 9.7's role, the seed
divisibility `ℓ ∣ z`, is supplied instead by Legendre's nonconsecutivity condition (A) at the
same prime `ℓ`. One prime `ℓ` therefore carries both cases: the all-even `Q_i` certificate
(Vandiver, `p ∤ h⁺`) and the Sophie Germain certificate (Case I and the seed of Case II), with
no upper bound on `ℓ`. `caseII_95` itself already takes `ℓ ∣ z` as a hypothesis and carries no
size bound.

The factorization and symmetry proofs are adapted from `CaseII95Descent`. The generic theorems
use no `sorry`, no project axiom and no `native_decide`; the concrete example (`p = 37`,
`ℓ = 3923 > 37² − 37`) lives in `flt-vandiver-primes` (`FltPrimes/FLT37Beyond.lean`).

Added in `afm-v2`; first written 2026-09-06 as a read-only check against `afm-v1`.
-/

set_option linter.style.nativeDecide false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace FltVandiver.JointAux

open CyclotomicNT FltVandiver FltVandiver.QiCert FltVandiver.Descent92
open FltVandiver.Descent95
open NumberField NumberField.IsCMField Polynomial UniqueFactorizationMonoid
open scoped NumberField

theorem lemma_9_6_zmod_joint {ℓ : ℕ} [Fact ℓ.Prime] {p k : ℕ} {μ : ZMod ℓ}
    (hpp : p.Prime)
    (hμ : IsPrimitiveRoot μ p) (hp2 : 2 < p) (hkp : ¬ p ∣ k) (hℓk : ℓ = k * p + 1)
    {zb : ZMod ℓ} (hz : zb ≠ 0) {a : ℕ} (ha : ¬ p ∣ a)
    {g s₁ s₂ : ZMod ℓ} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (he₁ : -(μ ^ a * zb) = g * s₁ ^ p)
    (he₂ : -(μ ^ ((p - 1) * a) * zb) = g * s₂ ^ p) : False := by
  have hppos : 0 < p := by omega
  have hμ0 : μ ≠ 0 := fun h0 => by
    have := hμ.pow_eq_one
    rw [h0, zero_pow (by omega : p ≠ 0)] at this
    exact zero_ne_one this
  have hg : g ≠ 0 := by
    intro h0
    rw [h0, zero_mul, neg_eq_zero] at he₁
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hz) he₁
  -- cross-multiplied key: s₁^p · μ^{(p−1)a} = s₂^p · μ^a, then clear μ powers
  have hμp : μ ^ (p * a) = 1 := by
    rw [pow_mul, hμ.pow_eq_one, one_pow]
  have hkey : g * (s₁ ^ p * μ ^ ((p - 1) * a)) = g * (s₂ ^ p * μ ^ a) := by
    have h1 : g * s₁ ^ p * μ ^ ((p - 1) * a) = -(μ ^ a * zb) * μ ^ ((p - 1) * a) := by
      rw [he₁]
    have h2 : g * s₂ ^ p * μ ^ a = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by
      rw [he₂]
    have h3 : -(μ ^ a * zb) * μ ^ ((p - 1) * a) = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by
      ring
    calc g * (s₁ ^ p * μ ^ ((p - 1) * a)) = g * s₁ ^ p * μ ^ ((p - 1) * a) := by ring
      _ = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by rw [h1, h3]
      _ = g * s₂ ^ p * μ ^ a := h2.symm
      _ = g * (s₂ ^ p * μ ^ a) := by ring
  have hkey' : s₁ ^ p * μ ^ ((p - 1) * a) = s₂ ^ p * μ ^ a :=
    mul_left_cancel₀ hg hkey
  -- multiply by μ^a: s₁^p = s₂^p · μ^{2a}
  have hup : s₁ ^ p = s₂ ^ p * μ ^ (2 * a) := by
    have h4 : s₁ ^ p * (μ ^ ((p - 1) * a) * μ ^ a) = s₂ ^ p * (μ ^ a * μ ^ a) := by
      calc s₁ ^ p * (μ ^ ((p - 1) * a) * μ ^ a)
          = (s₁ ^ p * μ ^ ((p - 1) * a)) * μ ^ a := by ring
        _ = (s₂ ^ p * μ ^ a) * μ ^ a := by rw [hkey']
        _ = s₂ ^ p * (μ ^ a * μ ^ a) := by ring
    have h5 : μ ^ ((p - 1) * a) * μ ^ a = 1 := by
      rw [← pow_add, show (p - 1) * a + a = p * a by
        have : 1 ≤ p := by omega
        zify [this]
        ring, hμp]
    have h6 : μ ^ a * μ ^ a = μ ^ (2 * a) := by
      rw [← pow_add, two_mul]
    rw [h5, h6, mul_one] at h4
    exact h4
  -- u := s₁/s₂ has u^p = μ^{2a}, an element of order p
  set u : ZMod ℓ := s₁ * s₂⁻¹ with hu
  have hupow : u ^ p = μ ^ (2 * a) := by
    rw [hu, mul_pow, hup, mul_comm (s₂ ^ p) (μ ^ (2 * a)), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hs₂, one_pow, mul_one]
  have hp2a : ¬ p ∣ 2 * a := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h2 | hA
    · exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
    · exact ha hA
  -- u^p = μ^{2a} ≠ 1, but u^{p²} = 1: u has order p², so p² ∣ ℓ − 1 = kp.
  have hne1 : μ ^ (2 * a) ≠ 1 := fun h1 => hp2a ((hμ.pow_eq_one_iff_dvd _).mp h1)
  have hupp : u ^ (p * p) = 1 := by
    rw [pow_mul, hupow, ← pow_mul, mul_comm (2 * a) p, pow_mul, hμ.pow_eq_one, one_pow]
  have hdvd_pp : orderOf u ∣ p ^ 2 := by
    rw [pow_two]
    exact orderOf_dvd_of_pow_eq_one hupp
  have hnot_p : ¬ orderOf u ∣ p := by
    intro hdp
    exact hne1 (by rw [← hupow]; exact orderOf_dvd_iff_pow_eq_one.mp hdp)
  have hord : orderOf u = p ^ 2 := by
    obtain ⟨m, hm2, hm⟩ := (Nat.dvd_prime_pow hpp).mp hdvd_pp
    interval_cases m
    · rw [pow_zero] at hm
      rw [hm] at hnot_p
      exact absurd (one_dvd p) hnot_p
    · rw [pow_one] at hm
      rw [hm] at hnot_p
      exact absurd dvd_rfl hnot_p
    · exact hm
  have hu0 : u ≠ 0 := mul_ne_zero hs₁ (inv_ne_zero hs₂)
  have hdvd_card : orderOf u ∣ ℓ - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hu0)
  rw [hord] at hdvd_card
  have hpk : p ∣ k := by
    have h7 : p * p ∣ k * p := by
      rw [← pow_two]
      exact hdvd_card.trans (dvd_of_eq (by omega))
    exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < p)).mp h7
  exact hkp hpk

variable {p : ℕ}

theorem aux_k_joint {ℓ : ℕ} [hℓpri : Fact ℓ.Prime] (hp2 : 2 < p)
    (hℓ : ℓ % p = 1) :
    ℓ = (ℓ - 1) / p * p + 1 ∧ 1 ≤ (ℓ - 1) / p := by
  have hℓ2 : 2 ≤ ℓ := hℓpri.out.two_le
  have hdvd : p ∣ ℓ - 1 := by
    have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt (by omega)
    have hmod : (1 : ℕ) ≡ ℓ [MOD p] := by
      unfold Nat.ModEq
      rw [h1, hℓ]
    exact (Nat.modEq_iff_dvd' (by omega)).mp hmod
  obtain ⟨k, hk⟩ := hdvd
  have hkval : (ℓ - 1) / p = k := by
    rw [hk]
    exact Nat.mul_div_cancel_left k (by omega)
  have hℓeq : ℓ = k * p + 1 := by
    rw [mul_comm]
    omega
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hk
      omega
    · exact h
  constructor
  · rw [hkval]
    exact hℓeq
  · rw [hkval]
    exact hk1

section Factor
variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]

theorem lemma_9_6_not_dvd_y_joint [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hvand : IsVandiverPrime p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (hyz : IsCoprime y z)
    {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime] (hℓ : ℓ % p = 1) (hkp : ¬ p ∣ (ℓ - 1) / p)
    (ht : redRoot p ℓ t ≠ 1) (ht0 : (t : ZMod ℓ) ≠ 0) :
    ¬ (ℓ : ℤ) ∣ y := by
  intro hly
  obtain ⟨hℓeq, _hk1⟩ := aux_k_joint hp hℓ
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓ ht ht0
  set φ : 𝓞 (CyclotomicField p ℚ) →ₐ[ℤ] ZMod ℓ := redHom hζ hμ with hφ
  -- ℓ ∤ z (coprimality with y)
  have hlz : ¬ (ℓ : ℤ) ∣ z := by
    intro hlz'
    obtain ⟨u, v, huv⟩ := hyz
    have h1 : (ℓ : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add (Dvd.dvd.mul_left hly u) (Dvd.dvd.mul_left hlz' v)
    have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have h3 := hℓpri.out.two_le
    omega
  have hzb : ((z : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hlz
  have hyb : ((y : ℤ) : ZMod ℓ) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hly
  -- the split at a = 1 and its reduction
  obtain ⟨γ, σ, hγreal, heq₁, heq₂⟩ := factor_split_96 hζ hp hvand hfer hx0 hpy hpz hyz 1
    (alpha_pth_power_96 hζ hp hvand hfer hx0 hpy hpz hyz 1)
  have hφY : φ ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((y : ℤ) : ZMod ℓ) := map_intCast φ y
  have hφZ : φ ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((z : ℤ) : ZMod ℓ) := map_intCast φ z
  have hφζ : φ hζ.toInteger = redRoot p ℓ t := redHom_zeta hζ hμ
  have he₁ : -(redRoot p ℓ t ^ 1 * ((z : ℤ) : ZMod ℓ))
      = φ ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * (φ σ) ^ p := by
    have h1 := congrArg φ heq₁
    rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ, hyb] at h1
    linear_combination h1
  have he₂ : -(redRoot p ℓ t ^ ((p - 1) * 1) * ((z : ℤ) : ZMod ℓ))
      = φ ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (φ (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ)) ^ p := by
    have h1 := congrArg φ heq₂
    rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ, hyb] at h1
    linear_combination h1
  -- nonvanishing of the σ-images
  have hμ0 : redRoot p ℓ t ≠ 0 := fun h0 => by
    have h1 := hμ.pow_eq_one
    rw [h0, zero_pow (by omega : p ≠ 0)] at h1
    exact zero_ne_one h1
  have hs₁ : φ σ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : p ≠ 0), mul_zero] at he₁
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hzb) (neg_eq_zero.mp he₁)
  have hs₂ : φ (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : p ≠ 0), mul_zero] at he₂
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hzb) (neg_eq_zero.mp he₂)
  exact lemma_9_6_zmod_joint hpri.out hμ hp hkp (by omega) hzb
    (by
      intro hdvd
      have := Nat.le_of_dvd one_pos hdvd
      omega) hs₁ hs₂ he₁ he₂

end Factor

theorem caseII_joint_top {p ℓ t : ℕ} [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime]
    (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hA : ∀ x y z : ZMod ℓ, x ^ p + y ^ p + z ^ p = 0 → x = 0 ∨ y = 0 ∨ z = 0)
    {x y z : ℤ} (hxyz : x ^ p + y ^ p = z ^ p)
    (hz0 : z ≠ 0) (hpz : (p : ℤ) ∣ z) (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y)
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z) :
    False := by
  have hp2 : 2 < p := by omega
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  haveI : NumberField.IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (CyclotomicField p ℚ) (S := {p})
      ⟨p, Set.mem_singleton p, hp2⟩
  set ζ : CyclotomicField p ℚ := IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)
    with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  -- the certificate gives Vandiver…
  have hvand : IsVandiverPrime p := qiVandiverBridge_all hcert
  -- …and, decoded, the ℓ-data
  simp only [vandiverCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcert
  obtain ⟨⟨⟨⟨hℓp, htk⟩, ht1⟩, hke⟩, hQcert⟩ := hcert
  have hQlist : ∀ i ∈ evenIndices p, qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1 :=
    fun i hi => of_decide_eq_true (List.all_eq_true.mp hQcert i hi)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two (by omega))
  have hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1 := by
    intro i hiev hi2 hip
    obtain ⟨j, hj⟩ := hiev
    have hidx : i = 2 * ((j - 1) + 1) := by omega
    have hjlt : j - 1 < (p - 3) / 2 := by omega
    rw [hidx]
    exact hQlist _ (mem_evenIndices hpodd hjlt)
  -- ℓ-arithmetic
  have hℓ2 : 2 ≤ ℓ := hℓpri.out.two_le
  have ht0 : (t : ZMod ℓ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : ℓ - 1 ≠ 0)] at ht1
    exact zero_ne_one ht1
  have htred : redRoot p ℓ t ≠ 1 := htk
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓp htred ht0
  obtain ⟨hℓeq, _hk1⟩ := aux_k_joint hp2 hℓp
  have hℓk : ℓ - 1 = (ℓ - 1) / p * p := by omega
  -- Generalized 9.6 excludes x and y. Nonconsecutivity then forces ℓ ∣ z.
  have hx0 : x ≠ 0 := fun h0 => hpx (h0 ▸ dvd_zero _)
  have hy0 : y ≠ 0 := fun h0 => hpy (h0 ▸ dvd_zero _)
  have hly : ¬ (ℓ : ℤ) ∣ y :=
    lemma_9_6_not_dvd_y_joint hζ hp2 hvand hxyz hx0 hpy hpz hyz hℓp hkp htred ht0
  have hlx : ¬ (ℓ : ℤ) ∣ x :=
    lemma_9_6_not_dvd_y_joint hζ hp2 hvand
      (by simpa [add_comm] using hxyz) hy0 hpx hpz hxz hℓp hkp htred ht0
  have hodd : Odd p := hpri.out.odd_of_ne_two (by omega)
  have hbar : (x : ZMod ℓ) ^ p + (y : ZMod ℓ) ^ p + (-(z : ZMod ℓ)) ^ p = 0 := by
    rw [hodd.neg_pow]
    have hh := congrArg (fun a : ℤ => (a : ZMod ℓ)) hxyz
    simp only [Int.cast_add, Int.cast_pow] at hh
    linear_combination hh
  have hℓz : (ℓ : ℤ) ∣ z := by
    rcases hA _ _ _ hbar with h | h | h
    · exact (hlx ((ZMod.intCast_zmod_eq_zero_iff_dvd x ℓ).mp h)).elim
    · exact (hly ((ZMod.intCast_zmod_eq_zero_iff_dvd y ℓ).mp h)).elim
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd z ℓ).mp (neg_eq_zero.mp h)
  exact caseII_95 hζ hp hvand hℓp hμ (k := (ℓ - 1) / p) hℓk hke hQall
    hxyz hz0 hpz hpx hpy hxy hxz hyz hℓz

theorem no_Int_Case2_joint {p ℓ t : ℕ} [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime]
    (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hA : ∀ x y z : ZMod ℓ, x ^ p + y ^ p + z ^ p = 0 → x = 0 ∨ y = 0 ∨ z = 0)
    {x y z : ℤ} (hcop : IsCoprime x y) (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z)
    (hz0 : z ≠ 0) (heq : x ^ p + y ^ p = z ^ p) : False := by
  have hppri : Nat.Prime p := Fact.out
  have hpne0 : p ≠ 0 := hppri.ne_zero
  have hpint : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hppri
  have hpx : ¬ (p : ℤ) ∣ x := by
    intro hdvd
    refine hpy (hpint.dvd_of_dvd_pow (n := p) ?_)
    have h1 : (p : ℤ) ∣ z ^ p - x ^ p :=
      dvd_sub (dvd_pow hpz hpne0) (dvd_pow hdvd hpne0)
    rwa [show z ^ p - x ^ p = y ^ p from by linear_combination -heq] at h1
  have hmix : ∀ {u v : ℤ}, (∀ q : ℤ, Prime q → q ∣ u → q ∣ v → False)
      → u ≠ 0 → IsCoprime u v := by
    intro u v hq hu
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    rcases Nat.eq_zero_or_pos (Int.gcd u v) with hg0 | hgpos
    · exact hu (Int.gcd_eq_zero_iff.mp hg0).1
    · obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqi : (q : ℤ) ∣ ((Int.gcd u v : ℕ) : ℤ) := by exact_mod_cast hqd
      exact hq _ (Nat.prime_iff_prime_int.mp hqp)
        (hqi.trans (Int.gcd_dvd_left u v)) (hqi.trans (Int.gcd_dvd_right u v))
  have hx0 : x ≠ 0 := by
    intro h0
    refine hpy (hpint.dvd_of_dvd_pow (n := p) ?_)
    have h1 : y ^ p = z ^ p := by
      rw [h0, zero_pow hpne0, zero_add] at heq
      exact heq
    rw [h1]
    exact dvd_pow hpz hpne0
  have hxz : IsCoprime x z := by
    refine hmix ?_ hx0
    intro q hq hqx hqz
    have h1 : q ∣ y ^ p := by
      rw [show y ^ p = z ^ p - x ^ p from by linear_combination heq]
      exact dvd_sub (dvd_pow hqz hpne0) (dvd_pow hqx hpne0)
    have h2 := hq.dvd_of_dvd_pow h1
    exact hq.not_unit (hcop.isUnit_of_dvd' hqx h2)
  have hyz : IsCoprime y z := by
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0] at hpy
      exact hpy (dvd_zero _)
    refine hmix ?_ hy0
    intro q hq hqy hqz
    have h1 : q ∣ x ^ p := by
      rw [show x ^ p = z ^ p - y ^ p from by linear_combination heq]
      exact dvd_sub (dvd_pow hqz hpne0) (dvd_pow hqy hpne0)
    have h2 := hq.dvd_of_dvd_pow h1
    exact hq.not_unit (hcop.isUnit_of_dvd' h2 hqy)
  exact caseII_joint_top hp hcert hkp hA heq hz0 hpz hpx hpy hcop hxz hyz

/-- **Case II via the 9.5 route** (symmetric integer form): under the single
Boolean certificate, `a^p + b^p = c^p` with `gcd = 1`, `abc ≠ 0`, `p ∣ abc` is
impossible. -/
theorem caseII_joint_int {p ℓ t : ℕ} [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime]
    (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hA : ∀ x y z : ZMod ℓ, x ^ p + y ^ p + z ^ p = 0 → x = 0 ∨ y = 0 ∨ z = 0)
    {a b c : ℤ} (hprod : a * b * c ≠ 0) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseII : (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  have hppri : Nat.Prime p := Fact.out
  have hpne0 : p ≠ 0 := hppri.ne_zero
  have hodd : Odd p := hppri.odd_of_ne_two (by omega)
  have hpint : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hppri
  have ha : a ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have hb : b ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have hc : c ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have div12 : ∀ q : ℤ, Prime q → q ∣ a → q ∣ b → q ∣ c := fun q hq hqa hqb => by
    have hd : q ∣ a ^ p + b ^ p := dvd_add (dvd_pow hqa hpne0) (dvd_pow hqb hpne0)
    rw [heq] at hd; exact hq.dvd_of_dvd_pow hd
  have div13 : ∀ q : ℤ, Prime q → q ∣ a → q ∣ c → q ∣ b := fun q hq hqa hqc => by
    have hd : q ∣ c ^ p - a ^ p := dvd_sub (dvd_pow hqc hpne0) (dvd_pow hqa hpne0)
    have hrw : c ^ p - a ^ p = b ^ p := by linear_combination -heq
    rw [hrw] at hd; exact hq.dvd_of_dvd_pow hd
  have div23 : ∀ q : ℤ, Prime q → q ∣ b → q ∣ c → q ∣ a := fun q hq hqb hqc => by
    have hd : q ∣ c ^ p - b ^ p := dvd_sub (dvd_pow hqc hpne0) (dvd_pow hqb hpne0)
    have hrw : c ^ p - b ^ p = a ^ p := by linear_combination -heq
    rw [hrw] at hd; exact hq.dvd_of_dvd_pow hd
  have hno_common : ∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b ∧ (q : ℤ) ∣ c)
      := by
    rintro q hqp ⟨hqa, hqb, hqc⟩
    have hqgcd : (q : ℤ) ∣ ({a, b, c} : Finset ℤ).gcd id := by
      apply Finset.dvd_gcd
      intros x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hqa
      · exact hqb
      · exact hqc
    rw [hgcd] at hqgcd
    have hu : IsUnit ((q : ℤ)) := isUnit_of_dvd_one hqgcd
    have hq1 : (q : ℤ) = 1 := by
      rcases Int.isUnit_iff.mp hu with h | h
      · exact h
      · have hge : (q : ℤ) ≥ 0 := Int.natCast_nonneg q
        omega
    have : q = 1 := by exact_mod_cast hq1
    exact hqp.one_lt.ne' this
  have coprime_of_div : ∀ {x y z : ℤ}, x ≠ 0 →
      (∀ q : ℤ, Prime q → q ∣ x → q ∣ y → q ∣ z) →
      (∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ x ∧ (q : ℤ) ∣ y ∧ (q : ℤ) ∣ z)) →
      IsCoprime x y := by
    intros x y z hx hdvdh hno
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    rcases Nat.eq_zero_or_pos (Int.gcd x y) with hz | hpos
    · exact hx (Int.gcd_eq_zero_iff.mp hz).1
    · obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqi : (q : ℤ) ∣ ((Int.gcd x y : ℕ) : ℤ) := by exact_mod_cast hqd
      have hqx : (q : ℤ) ∣ x := dvd_trans hqi (Int.gcd_dvd_left x y)
      have hqy : (q : ℤ) ∣ y := dvd_trans hqi (Int.gcd_dvd_right x y)
      have hqprime : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hqp
      have hqz : (q : ℤ) ∣ z := hdvdh _ hqprime hqx hqy
      exact hno q hqp ⟨hqx, hqy, hqz⟩
  have hab : IsCoprime a b := coprime_of_div ha div12 hno_common
  have hac : IsCoprime a c := coprime_of_div ha div13
    (fun q hq ⟨ha', hc', hb'⟩ => hno_common q hq ⟨ha', hb', hc'⟩)
  have hbc : IsCoprime b c := coprime_of_div hb div23
    (fun q hq ⟨hb', hc', ha'⟩ => hno_common q hq ⟨ha', hb', hc'⟩)
  rcases hpint.dvd_mul.mp hcaseII with hab' | hc'
  · rcases hpint.dvd_mul.mp hab' with hpa | hpb
    · have hpb : ¬ (p : ℤ) ∣ b := fun h => hpint.not_unit (hab.isUnit_of_dvd' hpa h)
      have heq' : c ^ p + (-b) ^ p = a ^ p := by
        rw [Odd.neg_pow hodd]; linear_combination -heq
      have hcop : IsCoprime c (-b) := (IsCoprime.symm hbc).neg_right
      have hnpb : ¬ (p : ℤ) ∣ (-b) := by rwa [dvd_neg]
      exact no_Int_Case2_joint hp hcert hkp hA hcop hnpb hpa ha heq'
    · have hpa : ¬ (p : ℤ) ∣ a := fun h => hpint.not_unit (hab.isUnit_of_dvd' h hpb)
      have heq' : (-a) ^ p + c ^ p = b ^ p := by
        rw [Odd.neg_pow hodd]; linear_combination -heq
      have hpc : ¬ (p : ℤ) ∣ c := fun h => hpint.not_unit (hbc.isUnit_of_dvd' hpb h)
      have hcop : IsCoprime (-a) c := hac.neg_left
      exact no_Int_Case2_joint hp hcert hkp hA hcop hpc hpb hb heq'
  · have hpb : ¬ (p : ℤ) ∣ b := fun h => hpint.not_unit (hbc.isUnit_of_dvd' h hc')
    exact no_Int_Case2_joint hp hcert hkp hA hab hpb hc' hc heq

/-- One joint witness proves FLT at p, with no upper bound on the auxiliary prime. -/
theorem fermatLastTheoremFor_of_joint_data
    {p ℓ t : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hp5 : 5 ≤ p)
    (hQi : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hA : ∀ x y z : ZMod ℓ, x ^ p + y ^ p + z ^ p = 0 → x = 0 ∨ y = 0 ∨ z = 0)
    (hB : ∀ t : ZMod ℓ, t ^ p ≠ (p : ZMod ℓ)) :
    FermatLastTheoremFor p := by
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc e
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime e hprod
  let d := ({a, b, c} : Finset ℤ).gcd id
  by_cases hcase : (p : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact caseII_joint_int (by omega) hQi hkp hA hprod' hgcd hcase e'
  · exact caseI_of_auxiliaryPrime ((Fact.out : p.Prime).odd_of_ne_two (by omega))
      (Fact.out : ℓ.Prime) hA hB hcase e'

/-- The concrete certificate interface: both checks refer to the same prime. -/
theorem fermatLastTheoremFor_of_joint_cert
    {p ℓ t : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [NeZero ℓ]
    (hp5 : 5 ≤ p)
    (hQi : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hSG : sgCert p ℓ = true) :
    FermatLastTheoremFor p := by
  obtain ⟨hA, hB⟩ := sgCert_imp hSG
  exact fermatLastTheoremFor_of_joint_data hp5 hQi hkp hA hB


/-- The remaining uniform supply statement for this combined route.
This is a proposition, not an axiom or a claimed theorem of existence. -/
def JointWitness (p : ℕ) : Prop :=
  ∃ (ℓ t : ℕ) (_ : Fact ℓ.Prime) (_ : NeZero ℓ),
    vandiverCert p ℓ t (evenIndices p) = true ∧
    sgCert p ℓ = true ∧ ¬ p ∣ (ℓ - 1) / p

/-- Uniform joint supply implies full FLT by the cyclotomic route. -/
theorem fermatLastTheorem_of_joint_supply
    (hsupply : ∀ p : ℕ, p.Prime → 5 ≤ p → JointWitness p) :
    FermatLastTheorem :=
  FermatLastTheorem.of_odd_primes fun p hp hodd => by
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hp3 : p = 3
    · subst p
      exact fermatLastTheoremThree
    · have hp5 : 5 ≤ p := by
        have hp2 := hp.two_le
        have hmod := Nat.odd_iff.mp hodd
        omega
      obtain ⟨ℓ, t, hℓ, hn, hQi, hSG, hkp⟩ := hsupply p hp hp5
      exact fermatLastTheoremFor_of_joint_cert hp5 hQi hkp hSG


end FltVandiver.JointAux
