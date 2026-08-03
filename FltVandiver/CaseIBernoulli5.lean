import FltVandiver.QiCertFast
import CyclotomicNT.BernoulliMod
import CyclotomicNT.HerbrandBernoulli

set_option linter.style.nativeDecide false

/-!
# Alternative Case I certificate via `p ∤ B_{p-5}` — fast power-sum computation

The Kummer/Mirimanoff route to Case I of FLT can be anchored at index `p-5` (not only the
`p-3` index handled by `CyclotomicNT.CaseIKummer.caseI_of_not_irregular`): if `p ∤ B_{p-5}`
then `p` is not irregular at that index, and Case I holds.

Discharging `¬ IsIrregularIndex p (p-5)` means checking `p ∤ num B_{p-5}`.  The *only*
computational path currently in the tree — the `bernZList` recurrence
(`IrrListCertFast.lean`) — is `O(p²)`(–`O(p³)`) with bignum binomials, hence infeasible at
`p = 2124679`.  This file supplies the **fast** discharge that makes a like-for-like
performance comparison against the Sophie-Germain (`sgCert`) Case I route possible.

**The identity.**  With `m := p-5` we have `1 ≤ m ≤ p-2` and `(p-1) ∤ m`, so `den B_m` is a
`p`-unit and (Herbrand's power-sum congruence `den_mul_sum_pow_modEq`)

  `(den B_m) · ∑_{a<p} aᵐ ≡ p · (num B_m)   [ZMOD p²]`.

Hence `p ∤ num B_m ⟺ ∑_{a<p} aᵐ ≢ 0 (mod p²)`.  We compute the right-hand sum with
`CertKernel.powModK` (proven `= b^e % m`), the same `O(log)` modular-powering primitive the
`Q_i`/`dVal` fast certs use at `p = 2124679` scale — the exact bignum `aᵐ` is never formed.

This module only *imports* existing modules; it edits none, so building it does not trigger a
`FLT2124679` recompile.  (The proof that `caseIBern5Cert` implies `¬ IsIrregularIndex` is the
next layer; this file establishes the computation and its cost.)
-/

namespace FltVandiver.CaseIBernoulli5

open CyclotomicNT (den_mul_sum_pow_modEq not_dvd_den_bernoulli)
open CyclotomicNT.QiCert (irrCheck bern IsIrregularIndex)

/-- Fast power-sum residue for `B_{p-5}`: `(∑_{a<p} a^{p-5}) mod p²`, each term via
`CertKernel.powModK` so the exact bignum `a^{p-5}` (millions of digits at large `p`) is never
formed.  By `den_mul_sum_pow_modEq` this is `≢ 0 (mod p²)` iff `p ∤ num B_{p-5}`. -/
def bernSumMod (p : ℕ) : ℕ :=
  (∑ a ∈ Finset.range p, CertKernel.powModK a (p ^ 2) (p - 5)) % (p ^ 2)

/-- The Case-I-at-`p-5` Bool certificate: a nonzero residue witnesses `p ∤ B_{p-5}`, i.e.
`¬ IsIrregularIndex p (p-5)`. -/
def caseIBern5Cert (p : ℕ) : Bool := bernSumMod p != 0

/-! ### Soundness bridge: `caseIBern5Cert p = true → ¬ IsIrregularIndex p (p-5)`

Turns the *verified computation* into a machine-checked Case-I hypothesis. The core is the
power-sum congruence `den_mul_sum_pow_modEq`; the only reindexing is `powModK`'s spec plus the
`Finset.sum_nat_mod` regrouping already used by `dValMod`. -/

/-- `bernSumMod` computes the honest power sum reduced mod `p²` (no exact bignum `aᵐ` formed):
`bernSumMod p = (∑_{a<p} a^{p-5}) mod p²`.  Mirror of `dValMod_eq`. -/
theorem bernSumMod_eq (p : ℕ) (hp : 0 < p) :
    bernSumMod p = (∑ a ∈ Finset.range p, a ^ (p - 5)) % p ^ 2 := by
  rw [bernSumMod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  exact Finset.sum_congr rfl fun a _ =>
    FltVandiver.QiCert.powModK_spec a (p ^ 2) (Nat.one_le_pow 2 p hp) (p - 5)

/-- **Soundness (numerator form).** A nonzero fast residue proves `p ∤ num B_{p-5}`. -/
theorem caseIBern5Cert_not_dvd_num (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (h : caseIBern5Cert p = true) : ¬ (p : ℤ) ∣ (bernoulli (p - 5)).num := by
  intro hdvd
  have hpp : p.Prime := Fact.out
  have hp0 : 0 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hm1 : 1 ≤ p - 5 := by omega
  have hmp : p - 5 ≤ p - 2 := by omega
  have hnd : ¬ (p - 1) ∣ (p - 5) := fun hd => by
    have := Nat.le_of_dvd (by omega) hd; omega
  -- power-sum congruence over ℤ: den · ∑ aᵐ ≡ p · num  [ZMOD p²]
  have hcong := den_mul_sum_pow_modEq (p := p) (m := p - 5) hp2 hm1 hmp
  -- den is a p-unit (von Staudt–Clausen, since (p-1) ∤ (p-5))
  have hden : ¬ (p : ℕ) ∣ (bernoulli (p - 5)).den := not_dvd_den_bernoulli hp2 hnd
  -- cert true ⇒ the Nat power sum is ≢ 0 mod p²
  have hne : bernSumMod p ≠ 0 := by simpa [caseIBern5Cert, bne_iff_ne] using h
  have hSnat : ¬ p ^ 2 ∣ ∑ a ∈ Finset.range p, a ^ (p - 5) := by
    rw [Nat.dvd_iff_mod_eq_zero, ← bernSumMod_eq p hp0]; exact hne
  -- cast the non-divisibility to ℤ
  have hSℤ : ¬ (p : ℤ) ^ 2 ∣ ∑ a ∈ Finset.range p, (a : ℤ) ^ (p - 5) := by
    have hcast : (∑ a ∈ Finset.range p, (a : ℤ) ^ (p - 5))
        = ((∑ a ∈ Finset.range p, a ^ (p - 5) : ℕ) : ℤ) := by push_cast; rfl
    rw [hcast, show ((p : ℤ) ^ 2) = ((p ^ 2 : ℕ) : ℤ) by push_cast; ring,
      Int.natCast_dvd_natCast]
    exact hSnat
  -- from `p ∣ num` we get `p² ∣ p·num`, hence (with the congruence) `p² ∣ den·S`
  have hp2num : (p : ℤ) ^ 2 ∣ (p : ℤ) * (bernoulli (p - 5)).num := by
    obtain ⟨k, hk⟩ := hdvd; exact ⟨k, by rw [hk]; ring⟩
  have hdiv : (p : ℤ) ^ 2 ∣
      ((bernoulli (p - 5)).den : ℤ) * ∑ a ∈ Finset.range p, (a : ℤ) ^ (p - 5) :=
    Int.modEq_zero_iff_dvd.mp (hcong.trans (Int.modEq_zero_iff_dvd.mpr hp2num))
  -- den coprime to p² ⇒ p² ∣ S, contradicting hSℤ
  have hcop : IsCoprime ((p : ℤ) ^ 2) ((bernoulli (p - 5)).den : ℤ) :=
    (Nat.Coprime.isCoprime (hpp.coprime_iff_not_dvd.mpr hden)).pow_left
  exact hSℤ (hcop.dvd_of_dvd_mul_left hdiv)

/-- **The Case-I certificate.** `caseIBern5Cert p = true` proves `p` is not irregular at index
`p-5`; this is exactly the hypothesis a `caseI_of_not_irregular`-style theorem consumes. -/
theorem caseI_not_irregular_bern5 (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (h : caseIBern5Cert p = true) : ¬ IsIrregularIndex p (p - 5) :=
  fun hirr => caseIBern5Cert_not_dvd_num p hp7 h hirr.2.2.2

/-! ### End-to-end demonstration

The full pipeline `native_decide` (cert) → bridge → Case-I hypothesis, at a cheap prime.
At `p = 2124679` the same line works with the `~18.5 s` `native_decide` in place of `59`'s. -/

example : ¬ IsIrregularIndex 59 (59 - 5) := by
  haveI : Fact (Nat.Prime 59) := ⟨by norm_num⟩
  exact caseI_not_irregular_bern5 59 (by norm_num) (by native_decide)

/-! ### Correctness cross-checks at small primes

`caseIBern5Cert p` should agree with `¬ (p is irregular at index p-5)`, which the memoized
`irrCheck` computes exactly via the `bern = bernoulli'` recurrence.  The mismatch list should
be empty; `37` (irregular at `32 = 37-5`) is the sanity anchor with residue `0`. -/

-- Mismatches between the fast cert and the exact irregularity check over primes `7 ≤ p < 120`.
-- Expected: `[]`.
#eval (List.range 120).filter (fun p =>
  decide (Nat.Prime p) && decide (7 ≤ p) && (caseIBern5Cert p != !(irrCheck p (p - 5))))

#eval bernSumMod 37        -- expect 0  (37 ∣ B₃₂,  32 = 37 - 5)
#eval caseIBern5Cert 37    -- expect false
#eval caseIBern5Cert 59    -- expect true  (59 regular at index 54)

end FltVandiver.CaseIBernoulli5
