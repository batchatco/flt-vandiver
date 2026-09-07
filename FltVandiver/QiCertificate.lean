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

`vandiverCert p ℓ t idx` is a `Bool` that `native_decide` evaluates instantly. The argument `idx`
is the list of indices `i` at which the test `Q_i^k ≠ 1` is run. The library always instantiates
it at `evenIndices p`, every even `2 ≤ i ≤ p − 3`, and that is what the bridge consumes: the
all-even certificate closes `p ∤ h⁺` through Washington Prop 8.18 and Thm 8.14 alone, with no use
of Thm 8.16 or Cor 8.19 and no dependence on the irregular-index set. Running only over the
irregular indices (Washington's own criterion, Cor 8.19) is a weaker use of the same `Bool`; the
example below shows it at `p = 37`, `(ℓ, t) = (149, 2)`, irregular index `32`.

**Piece 2** — the classical bridge `vandiverCert p ℓ t (evenIndices p) = true → IsVandiverPrime p`
(Washington 8.14/8.18, a substantial but p-adic-L-free cyclotomic-unit/Gauss-sum argument on
`CyclotomicNT.RegularPrimes.IsVandiverPrime`) is **not** in this file; it is supplied by the
`qiVandiverBridge` lemmas.

## Formula notes (load-bearing)
* `t` need only satisfy `(t,ℓ)=1` and `t^k ≢ 1 mod ℓ` (a nontrivial `p`-th root of unity); it
  need **not** be a primitive root.
* The prefactor exponent is `k·d/2 = (k*d)/2`, computed as **one** division of the full product
  (exact because `k = (ℓ−1)/p` is even). Do **not** write `k*(d/2)`: `d` is odd, so `d/2`
  truncates in `ℕ` and drops a factor.
* The certifying condition is the **negation** `Q_i^k ≠ 1` for every listed `i`. -/

namespace FltVandiver.QiCert

open Finset

/-- `d_i = Σ_{a=1}^{(p-1)/2} a^(p-i)` (Washington Prop 8.18). -/
def dVal (p i : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), a ^ (p - i)

/-- `Q_i ∈ ZMod ℓ` (Washington Prop 8.18):
`Q_i = t^{-(k·d)/2} · ∏_{b=1}^{(p-1)/2} (t^{k b} − 1)^{b^{p-1-i}}`, with `k = (ℓ−1)/p`.
`Fact ℓ.Prime` makes `ZMod ℓ` a field, supplying `⁻¹` and `DecidableEq`.

`Q_i` is **not** the image `Ē_i` of the eigen-unit `E_i` modulo the prime `𝔩` above `ℓ` at which
`ζ ≡ μ := t^k`. With `d'_i = Σ_{a=1}^{(p-1)/2} a^{p-1-i}` the definitions give
`Q_i / Ē_i = (t^{(ℓ-1)/2})^{d_i} · (μ − 1)^{d'_i}`: the `ζ`-prefactors of the `ξ_a` and the
prefactor `t^{-k d_i/2}` combine to `(t^{(ℓ-1)/2})^{d_i}` times a power of `μ` with exponent
divisible by `p`, and the denominators `ζ − 1` of the `ξ_a` supply `(μ − 1)^{d'_i}`. The first
factor is `±1` (`t^{ℓ-1} = 1`) and dies under the `k`-th power because `k` is even; the second is
a `p`-th power (`p ∣ d'_i`) and dies because `pk = ℓ − 1`. So `Ē_i^k = Q_i^k`, which is all the
test consumes and what the bridge proves. Example: `p = 5, ℓ = 11, t = 2, i = 2` gives `Ē_2 = 4`,
`Q_2 = 7`, common square `5`. -/
def qi (p i ℓ t : ℕ) [Fact ℓ.Prime] : ZMod ℓ :=
  let k := (ℓ - 1) / p
  let half := (p - 1) / 2
  (t : ZMod ℓ)⁻¹ ^ (k * dVal p i / 2) *
    ∏ b ∈ Finset.Icc 1 half, ((t : ZMod ℓ) ^ (k * b) - 1) ^ (b ^ (p - 1 - i))

/-- The certificate: `ℓ ≡ 1 (mod p)`, `t^k ≠ 1`, **`t` a unit mod `ℓ`** (`t^{ℓ-1}=1`), **`k` even**
(`2 ∣ k`), and `Q_i^k ≠ 1` for every index `i` in `irr`. The library runs it at
`irr = evenIndices p` (every even `2 ≤ i ≤ p − 3`); when `true` there, Washington Prop 8.18 gives
`E_i ∉ (E⁺)^p` for every even `i`, and Thm 8.14 gives `p ∤ h⁺`, i.e. `IsVandiverPrime p` (via the
bridge, which uses neither Thm 8.16 nor Cor 8.19). At `irr` = the irregular indices the same
`Bool` is Washington's Cor 8.19 criterion, which the library does not rely on.
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
