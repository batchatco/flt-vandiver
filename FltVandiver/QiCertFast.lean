import FltVandiver.QiCertificate
import CertKernel
import Mathlib.FieldTheory.Finite.Basic

/-!
# The fast `Q_i` certificate: exponents reduced mod `ℓ − 1`

`QiCert.qi` raises each factor `t^{kb} − 1` to the **exact bignum** `b^{p−1−i}`
(`~(p−1−i)·log₂ b` bits — tens of thousands of `ZMod ℓ` squarings per factor);
at `p = 3511` that is hours of CPU per index slice.  By Fermat's little theorem a
nonzero element of `ZMod ℓ` satisfies `x^{ℓ−1} = 1`, so the exponent can be
reduced mod `ℓ − 1` — computed by modular powering (`CertKernel.powModK`),
`O(log)` instead of `O(exponent)`.  Same for the `t^{−kd/2}` prefactor.

`vandiverCertFast` additionally checks every factor is nonzero (the hypothesis
Fermat needs), and the **one-directional bridge** `vandiverCert_of_fast` feeds
the original `vandiverCert` Bool — `qiVandiverBridge_all` and the existing glue
are untouched.
-/

namespace FltVandiver.QiCert

/-- Correctness of the precompiled square-and-multiply kernel (relocated from
the retired log-kernel bridge). -/
theorem powModK_spec (b m : ℕ) (_hm : 1 ≤ m) :
    ∀ e, CertKernel.powModK b m e = b ^ e % m := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    match e with
    | 0 =>
      rw [CertKernel.powModK, pow_zero]
    | (e + 1) =>
      rw [CertKernel.powModK]
      have ihh := ih ((e + 1) / 2) (Nat.div_lt_self (Nat.succ_pos e) Nat.one_lt_two)
      rw [ihh]
      by_cases hpar : (e + 1) % 2 = 1
      · rw [if_pos hpar]
        conv_rhs => rw [show e + 1 = (e + 1) / 2 + (e + 1) / 2 + 1 from by omega]
        rw [pow_succ, pow_add, Nat.mul_mod (b ^ ((e + 1) / 2) * b ^ ((e + 1) / 2)) b m,
          Nat.mul_mod (b ^ ((e + 1) / 2)) (b ^ ((e + 1) / 2)) m]
      · rw [if_neg hpar]
        conv_rhs => rw [show e + 1 = (e + 1) / 2 + (e + 1) / 2 from by omega]
        rw [pow_add, Nat.mul_mod (b ^ ((e + 1) / 2)) (b ^ ((e + 1) / 2)) m]


open Finset

/-- Fermat reduction: for `x ≠ 0` in `ZMod ℓ` (`ℓ` prime), `x^n = x^{n mod (ℓ−1)}`. -/
theorem pow_mod_card_sub_one {ℓ : ℕ} [Fact ℓ.Prime] (x : ZMod ℓ) (hx : x ≠ 0)
    (n : ℕ) : x ^ n = x ^ (n % (ℓ - 1)) := by
  conv_lhs => rw [← Nat.div_add_mod n (ℓ - 1)]
  rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]

/-- Fast modular `dVal`: `(∑_{a=1}^{(p−1)/2} a^(p−i)) mod m`, each term reduced by
`powModK` so the exact bignum `a^(p−i)` (millions of digits at large `p`) is never
formed — the prefactor analogue of the `powModK` reduction already used in the product. -/
def dValMod (p i m : ℕ) : ℕ :=
  (∑ a ∈ Finset.Icc 1 ((p - 1) / 2), CertKernel.powModK a m (p - i)) % m

theorem dValMod_eq {p i m : ℕ} (hm : 1 ≤ m) : dValMod p i m = dVal p i % m := by
  rw [dValMod, dVal]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => powModK_spec a m hm (p - i))

/-- `Q_i` with all huge exponents reduced mod `ℓ − 1` (modular powering) —
including the `t⁻¹` prefactor, whose exponent uses the modular `dValMod`
(valid because the cert checks `2 ∣ k`; see `vandiverCert_of_fast`). -/
def QiFast (p i ℓ t : ℕ) [Fact ℓ.Prime] : ZMod ℓ :=
  let k := (ℓ - 1) / p
  let half := (p - 1) / 2
  (t : ZMod ℓ)⁻¹ ^ (k / 2 * dValMod p i (ℓ - 1) % (ℓ - 1)) *
    ∏ b ∈ Finset.Icc 1 half,
      ((t : ZMod ℓ) ^ (k * b) - 1) ^ (CertKernel.powModK b (ℓ - 1) (p - 1 - i))

/-- The fast certificate: the four structural checks of `vandiverCert`, plus
nonvanishing of every factor (the Fermat hypothesis), plus the `Q_i^k ≠ 1` test
over `QiFast`. -/
def vandiverCertFast (p ℓ t : ℕ) [Fact ℓ.Prime] (irr : List ℕ) : Bool :=
  let k := (ℓ - 1) / p
  let half := (p - 1) / 2
  (ℓ % p == 1) &&
  decide ((t : ZMod ℓ) ^ k ≠ 1) &&
  decide ((t : ZMod ℓ) ^ (ℓ - 1) = 1) &&
  decide (2 ∣ k) &&
  ((List.range half).all fun b0 =>
    decide ((t : ZMod ℓ) ^ (k * (b0 + 1)) - 1 ≠ 0)) &&
  irr.all (fun i => decide ((QiFast p i ℓ t) ^ k ≠ 1))

/-- **The bridge**: a true fast certificate yields the original `vandiverCert`
Bool — so `qiVandiverBridge_all` and all downstream glue apply unchanged. -/
theorem vandiverCert_of_fast {p ℓ t : ℕ} [Fact ℓ.Prime] {irr : List ℕ}
    (h : vandiverCertFast p ℓ t irr = true) :
    vandiverCert p ℓ t irr = true := by
  haveI hℓ : Fact (Nat.Prime ℓ) := inferInstance
  rw [vandiverCertFast] at h
  rw [vandiverCert]
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨hl, ht⟩, hu⟩, h2k⟩, hfac⟩, hqi⟩ := h
  refine ⟨⟨⟨⟨hl, ht⟩, hu⟩, h2k⟩, fun i hi => ?_⟩
  have htne : (t : ZMod ℓ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by
      have := hℓ.out.two_le
      omega)] at hu
    exact one_ne_zero hu.symm
  have hinv_ne : ((t : ZMod ℓ))⁻¹ ≠ 0 := inv_ne_zero htne
  have hQ : qi p i ℓ t = QiFast p i ℓ t := by
    simp only [qi, QiFast]
    congr 1
    · -- prefactor: `k·dVal/2` (exact) matches `k/2·dValMod` (modular), using `2 ∣ k`
      rw [pow_mod_card_sub_one _ hinv_ne]
      congr 1
      have hm1 : 1 ≤ ℓ - 1 := by have := hℓ.out.two_le; omega
      rw [dValMod_eq hm1]
      obtain ⟨c, hc⟩ := h2k
      rw [hc, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2),
        Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]
      exact (Nat.ModEq.mul_left c (Nat.mod_modEq (dVal p i) (ℓ - 1))).symm
    · refine Finset.prod_congr rfl fun b hb => ?_
      rw [Finset.mem_Icc] at hb
      have hbne : (t : ZMod ℓ) ^ ((ℓ - 1) / p * b) - 1 ≠ 0 := by
        have := hfac (b - 1) (List.mem_range.mpr (by omega))
        rw [show b - 1 + 1 = b from by omega] at this
        exact this
      rw [pow_mod_card_sub_one _ hbne,
        powModK_spec b (ℓ - 1)
          (by have := hℓ.out.two_le; omega)]
  rw [hQ]
  exact hqi i hi

end FltVandiver.QiCert
