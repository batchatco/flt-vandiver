import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum.Prime

-- `native_decide` is the certificate mechanism of this development: compiler-trusted
-- boolean evaluation behind kernel-checked soundness bridges (see the trust note in
-- the README). The linter ban is Mathlib-specific; here the usage is by design.
set_option linter.style.nativeDecide false

/-!
# The `Q_i` Vandiver certificate (Piece 1: the computable test)

This file is **Piece 1** of the `Q_i` route to discharging `IsVandiverPrime p` for a specific
prime (target `p = 37`) by a finite, pure-`ZMod ℓ` computation — **no p-adic L / Iwasawa**.
Source: Washington, *Introduction to Cyclotomic Fields*, §8.3 (Prop 8.18, Cor 8.19).

`vandiverCert p ℓ t irr` is a `Bool` that `native_decide` evaluates instantly; for `p = 37` it
fires at `(ℓ, t) = (149, 2)` with irregular index list `[32]`, so `IsVandiverPrime 37` holds
*provided* the bridge lemma (Piece 2) is supplied.

**Piece 2** — the classical bridge `vandiverCert … = true → IsVandiverPrime p` (Washington
8.14/8.16/8.18, a substantial but p-adic-L-free cyclotomic-unit/Gauss-sum argument on
`CyclotomicNT.RegularPrimes.IsVandiverPrime`) is **not** in this file; it is supplied by the
`qiVandiverBridge` lemmas.

## Formula notes (load-bearing)
* `t` need only satisfy `(t,ℓ)=1` and `t^k ≢ 1 mod ℓ` (a nontrivial `p`-th root of unity); it
  need **not** be a primitive root.
* The prefactor exponent is `k·d/2 = (k*d)/2`, computed as **one** division of the full product
  (exact because `k = (ℓ−1)/p` is even). Do **not** write `k*(d/2)`: `d` is odd, so `d/2`
  truncates in `ℕ` and drops a factor.
* The certifying condition is the **negation** `Q_i^k ≠ 1` for every irregular `i`. -/

namespace FltVandiver.QiCert

open Finset

/-- `d_i = Σ_{a=1}^{(p-1)/2} a^(p-i)` (Washington Prop 8.18). -/
def dVal (p i : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), a ^ (p - i)

/-- `Q_i ∈ ZMod ℓ` (Washington Prop 8.18):
`Q_i = t^{-(k·d)/2} · ∏_{b=1}^{(p-1)/2} (t^{k b} − 1)^{b^{p-1-i}}`, with `k = (ℓ−1)/p`.
`Fact ℓ.Prime` makes `ZMod ℓ` a field, supplying `⁻¹` and `DecidableEq`. -/
def qi (p i ℓ t : ℕ) [Fact ℓ.Prime] : ZMod ℓ :=
  let k := (ℓ - 1) / p
  let half := (p - 1) / 2
  (t : ZMod ℓ)⁻¹ ^ (k * dVal p i / 2) *
    ∏ b ∈ Finset.Icc 1 half, ((t : ZMod ℓ) ^ (k * b) - 1) ^ (b ^ (p - 1 - i))

/-- The certificate: `ℓ ≡ 1 (mod p)`, `t^k ≠ 1`, **`t` a unit mod `ℓ`** (`t^{ℓ-1}=1`), **`k` even**
(`2 ∣ k`), and `Q_i^k ≠ 1` for every irregular index `i`.  When `true` (and `irr` is the list of
irregular indices), Washington Cor 8.19 gives `p ∤ h⁺` — i.e. `IsVandiverPrime p` (via the bridge).
The `t^{ℓ-1}=1` and `2 ∣ k` clauses make `μ = t^k` a primitive `p`-th root and the `t^{-k d/2}`
prefactor exact — exactly the validity conditions Prop 8.18 needs. -/
def vandiverCert (p ℓ t : ℕ) [Fact ℓ.Prime] (irr : List ℕ) : Bool :=
  let k := (ℓ - 1) / p
  (ℓ % p == 1) &&
  decide ((t : ZMod ℓ) ^ k ≠ 1) &&
  decide ((t : ZMod ℓ) ^ (ℓ - 1) = 1) &&
  decide (2 ∣ k) &&
  irr.all (fun i => decide ((qi p i ℓ t) ^ k ≠ 1))

section Verification

/-- `149 = 4·37 + 1` is prime, so `ZMod 149` is a field. -/
instance : Fact (Nat.Prime 149) := ⟨by norm_num⟩

/-- The single irregular index of `37` is `32` (`37 ∣ num B₃₂`); `Q₃₂ ≡ 146 (mod 149)`. -/
example : qi 37 32 149 2 = 146 := by native_decide

/-- `Q₃₂^k = 81 ≢ 1 (mod 149)` with `k = (149−1)/37 = 4`, so the test fires at index `32`. -/
example : qi 37 32 149 2 ^ ((149 - 1) / 37) = 81 := by native_decide

end Verification

section OtherSmallIrregularPrimes

/-! Additional explicit Q_i certificates for the next few irregular primes (for illustration and
    future wiring).
   These use the same general `vandiverCert`/`qi`. The corresponding `IsIrregularIndex` lists
   can be proven analogously to `irregularIndices_37` once BernoulliMod is extended or per-p
   `native_decide` facts are added. The bridge (`qiVandiverBridge`) is general in `p`.

   **Choice of `ℓ`.** For each `p` we take the *smallest* prime `ℓ ≡ 1 (mod 2p)`; it passes the
   `Q_i` test with `t = 2` in every case here (and empirically for every irregular `p < 2000`).
   `ℓ` often coincides with the Case I auxiliary prime `q` of `SophieGermain.lean` — here for
   `p = 37, 67, 131, 149, 157` — and that is no accident: both searches scan the *same*
   progression `1 (mod 2p)` from the bottom (Case I needs `q = 2Np + 1`; the `Q_i` test needs
   `k = (ℓ−1)/p` even, automatic for odd `p`), and the `Q_i` test passes at almost every
   candidate (it fails only when a cyclotomic unit is accidentally a `p`-th power mod `ℓ`,
   density ≈ `1/p`).  So whichever prime the pickier Case I search settles on, the `Q_i` test
   almost always holds there too.  When the two differ (`p = 59, 101, 103`) it is because the
   smallest prime in the progression fails `sgCert` while passing the `Q_i` test.  The overlap
   is statistical, NOT structural: there is no implication `sgCert p q → vandiverCert p q`
   (counterexample: `q = 49853` passes Case I for `p = 103` but fails the `Q_i` test), and no
   uniform-in-`p` guarantee (that would be stronger than the open Sophie-Germain existence
   question). -/

/-- ℓ=709 = 12·59 +1 for p=59, t=2: smallest prime ≡ 1 (mod 2·59) (fails `sgCert`, so
`caseI_59` uses `q = 827`). -/
instance : Fact (Nat.Prime 709) := ⟨by norm_num⟩
example : vandiverCert 59 709 2 [44] = true := by native_decide

/-- ℓ=269 = 4·67 +1 for p=67, t=2: smallest prime ≡ 1 (mod 2·67) (= `caseI_67`'s `q`). -/
instance : Fact (Nat.Prime 269) := ⟨by norm_num⟩
example : vandiverCert 67 269 2 [58] = true := by native_decide

/-- ℓ=607 = 6·101 +1 for p=101, t=2: smallest prime ≡ 1 (mod 2·101) (fails `sgCert`, so
`caseI_101` uses `q = 809`). -/
instance : Fact (Nat.Prime 607) := ⟨by norm_num⟩
example : vandiverCert 101 607 2 [68] = true := by native_decide

/-- ℓ=619 = 6·103 +1 for p=103, t=2: smallest prime ≡ 1 (mod 2·103) (fails `sgCert`, so
`caseI_103` uses `q = 1031`). -/
instance : Fact (Nat.Prime 619) := ⟨by norm_num⟩
example : vandiverCert 103 619 2 [24] = true := by native_decide

/-- ℓ=263 = 2·131 +1 for p=131, t=2: smallest prime ≡ 1 (mod 2·131) (= `caseI_131`'s `q`). -/
instance : Fact (Nat.Prime 263) := ⟨by norm_num⟩
example : vandiverCert 131 263 2 [22] = true := by native_decide

/-- ℓ=1193 = 8·149 +1 for p=149, t=2: smallest prime ≡ 1 (mod 2·149) (= `caseI_149`'s `q`). -/
instance : Fact (Nat.Prime 1193) := ⟨by norm_num⟩
example : vandiverCert 149 1193 2 [130] = true := by native_decide

/-- ℓ=1571 = 10·157 +1 for p=157 (index-2), t=2: smallest prime ≡ 1 (mod 2·157)
(= `caseI_157`'s `q`). -/
instance : Fact (Nat.Prime 1571) := ⟨by norm_num⟩
example : vandiverCert 157 1571 2 [62, 110] = true := by native_decide

end OtherSmallIrregularPrimes

end FltVandiver.QiCert
