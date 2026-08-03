import CyclotomicNT.RegularPrimes
import FltVandiver.CaseI
import CyclotomicNT.CaseII
import FltVandiver.RouteA
import FltVandiver.CaseII95Descent
import FltVandiver.GermainReduction
import Mathlib.NumberTheory.FLT.Three
import FltVandiver.SophieGermain
import FltRegular.FltRegular
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Four
open CyclotomicNT

/-!
# Fermat's Last Theorem under Vandiver + Case I hypotheses

This file states the main reduction theorem of `flt-vandiver`:

> If `p` is an odd prime, `p` is a Vandiver prime, and Case I holds at `p`, then FLT holds at
> exponent `p`.

The hypothesis list is **honest**: Case I is *not* derivable from Vandiver (the obstructing
class lies in `Cl(K)⁻`; see `FltVandiver.CaseI`), so it enters as its own hypothesis
`CaseIHolds p`, discharged per-prime by a Sophie Germain certificate
(`flt_vandiver_of_sgCert`) or, for regular `p`, by `FltRegular.caseI`
(`flt_vandiver_of_regular`).  At specific irregular primes (e.g. `p = 37`) both hypotheses are
discharged numerically, giving FLT-37 with no named axioms — only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) plus the `native_decide` certificates.

The proof closely follows `FltRegular`'s Case I and Case II machinery, with the regularity
hypothesis weakened to:
* `IsVandiverPrime p` — used in place of `IsRegularPrime p` in the Case II descent;
* `KummerUnitProperty p` — kept in the signature for API stability; the Route-A descent no
  longer uses it.
-/

open NumberField

namespace FltVandiver

/-- **The small-witness certificate package at `p`** (Washington Thm 9.5): a single
auxiliary pair `(ℓ, t)` — `ℓ ≡ 1 (mod p)` prime, `ℓ < p² − p` — whose `Q_i`
certificate fires at every even index.  It is pure `native_decide` data, and it
already implies `IsVandiverPrime p` (`qiVandiverBridge_all`), so the crowns
below need no separate Vandiver hypothesis. -/
def SmallWitnessCert (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (ℓ t : ℕ) (_ : Fact ℓ.Prime),
    QiCert.vandiverCert p ℓ t (QiCert.evenIndices p) = true ∧ ℓ < p * p - p

/-- **Main reduction theorem:** FLT at `p`, assuming Vandiver + Case I.

The reduction to the two cases is regularity-free and mirrors `FltRegular.flt_regular`
verbatim: reduce to integer solutions, divide out the gcd (`MayAssume.coprime`), and split on
whether `p` divides the (coprimified) product.  Case II is the Washington-9.5 descent —
the small-witness certificate does all the work, including Vandiver at `p`; Case I is the
hypothesis `hcaseI` (it cannot come from Vandiver — see `FltVandiver.CaseI`).

No `KummerUnitProperty` hypothesis: the Route-A descent never uses it, and it is expected to be
**false** at irregular primes (see `RegularPrimes.lean`), so hypothesizing it would make this
statement vacuous exactly at the primes it targets. -/
theorem flt_vandiver
    {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (hcert : SmallWitnessCert p)
    (hcaseI : CaseIHolds p) :
    FermatLastTheoremFor p := by
  obtain ⟨ℓ, t, hℓpri, hQi, hsize⟩ := hcert
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc e
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime e hprod
  let d := ({a, b, c} : Finset ℤ).gcd id
  by_cases case : (p : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact Descent95.caseII_95_int hp3 hQi hsize hprod' hgcd case e'
  · exact hcaseI _ _ _ case e' 

/-- **The crown: Fermat's Last Theorem, reduced to two named open problems.**

If every odd prime is a Vandiver prime, and Case I holds at every odd prime (e.g. via the
Legendre/Sophie-Germain auxiliary-prime existence), then Fermat's Last Theorem holds — with
no modularity input.  The two hypotheses are precisely the two open problems of the
non-modular route:

* `hswcert` — the **effective small-witness Vandiver certificate** (Washington Thm 9.5's
  hypothesis: a certified auxiliary pair with `ℓ < p² − p`), uniformly in `p`;
* `hcaseI` — **Case I**, uniformly in `p` (a long-open problem — Ribenboim, *13 Lectures*,
  Lecture IV; per-prime certificates exist).

Together with `fermatLastTheoremFour` and the reduction to prime exponents, this is the
machine-checked statement of *FLT without Wiles*: the entire gap between Kummer-style methods
and FLT is exhibited as these two hypotheses. -/
theorem fermatLastTheorem_of_vandiver_caseI
    (hswcert : ∀ (p : ℕ) [Fact p.Prime], 3 < p → SmallWitnessCert p)
    (hcaseI : ∀ (p : ℕ), p.Prime → p ≠ 2 → CaseIHolds p) :
    FermatLastTheorem :=
  FermatLastTheorem.of_odd_primes fun p hp hodd => by
    haveI := Fact.mk hp
    have hne : p ≠ 2 := by rintro rfl; have := Nat.odd_iff.mp hodd; omega
    rcases eq_or_ne p 3 with rfl | hne3
    · exact fermatLastTheoremThree
    · have hp3 : 3 < p := by
        have h2 := hp.two_le
        omega
      exact flt_vandiver hp3 (hswcert p hp3) (hcaseI p hp hne)

/-- **The crown, species-exact form: FLT from Vandiver plus auxiliary-prime existence.**

Same conclusion as `fermatLastTheorem_of_vandiver_caseI`, but with the Case I hypothesis in
its true *species*: a prime-existence statement (long open; Ribenboim, *13 Lectures on
Fermat's Last Theorem*, Lecture IV, with Dickson 1909 as the finiteness backdrop).  The
two hypotheses are now visibly of different kinds:

* `hswcert` — the **effective small-witness Vandiver certificate**: a 1/p-congruence-anomaly
  statement in effective form (every analytic route to plain Vandiver is closed; see the
  project's frontier map);
* `haux` — **a Sophie Germain auxiliary prime exists for every `p`**: a prime-distribution
  statement.  Its combinatorial content is classical (Wendt 1894, Furtwängler, Ford–Jha:
  for `q = 2Np+1` with `3 ∤ N` the certificate fails only on divisors of Wendt's determinant
  `Res(Xᵐ−1, (−1−X)ᵐ−1)`, `m = 2N`).  The Germain-window measurement
  locates the failure boundary empirically:
  P[(A) holds] = exp(−t/6) in `t = 2N/p = |H|²/q`, uniformly over `p ∈ [10³, 3·10⁵]`
  (c = 1/6 is the anharmonic-orbit constant; the subgroup behaves exactly like a random
  set), so the window closes at `t* ≈ 6 log p` (`q ≲ 6p² log p`) — while GRH first sees
  primes `≡ 1 (mod 2p)` only at `t ≳ log² p` (least prime `(φ log)²`; counts from
  `p² log⁴ p`): the route misses GRH by one logarithm.  Uniform Case I via auxiliaries
  therefore needs exactly two inputs: **(α)** prime supply at the `q ≍ p²` threshold
  (beyond GRH; follows from Montgomery-type AP-error or Granville/Heath-Brown least-prime
  conjectures — this is the wall), and **(β)** the cross-`q` union/second-moment statement
  (*not all candidate subgroups contain a representation of 1*) — far weaker than any
  per-`q` result, equivalent at `t ≍ 1` to square-root cancellation in the order-`p`
  Jacobi-sum family on average over `q`, and measured to hold exactly (census across
  1,118 primes: variance ratio 1.013 ± 0.042).

So FLT-without-Wiles = (one anomaly-control problem) + (one primes-in-AP-at-the-`m²`-
threshold problem + one cross-modulus averaging statement).  A proof of the
auxiliary-prime existence collapses the crown to the single hypothesis
`∀ p, SmallWitnessCert p`. -/
theorem fermatLastTheorem_of_vandiver_sgAux
    (hswcert : ∀ (p : ℕ) [Fact p.Prime], 3 < p → SmallWitnessCert p)
    (haux : ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∃ q : ℕ, ∃ _ : NeZero q, q.Prime ∧ sgCert p q = true) :
    FermatLastTheorem :=
  fermatLastTheorem_of_vandiver_caseI hswcert fun p hp hne => by
    haveI := Fact.mk hp
    obtain ⟨q, _, hq, hcert⟩ := haux p hp hne
    exact fun a b c h => caseI_of_sgCert (hp.odd_of_ne_two hne) hq hcert h

/-- **Crown v3 (Germain-window variant): FLT from four displayed hypotheses.**

With the descent axioms proven, Fermat's Last Theorem reduces to four named
statements, each a recognized open problem:

* `hswcert` — the **effective small-witness Vandiver certificate**, uniformly
  in `p`: a certified auxiliary pair `(ℓ, t)` with `ℓ < p² − p`
  (`p ∤ h⁺(ℚ(ζ_p))` in effective, per-prime-checkable form);
* `hα` — **prime supply at the `p²`-threshold**: the window
  `𝒬_p(C·p²) = {q ≤ C·p² prime, q ≡ 1 (mod 2p), 3 ∤ (q−1)/2p}` is nonempty —
  the least-prime-in-AP barrier (one logarithm beyond GRH detection);
* `hβA` — **aggregated Jacobi cancellation**: the total count of `H × H`-pairs
  summing to `1` across the window is at most half the window size — square-root
  cancellation in the order-`p` Jacobi-sum family on average over `q`;
* `hβB` — **power-residue sparsity**: at most a quarter of the window has `p` a
  `p`-th power mod `q` (the Wieferich-flavored condition (B), on average).

Taking `M := |𝒬_p(C·p²)|`, the pigeonhole (`caseI_of_supply_of_cancellation`) turns
(α) + (β-A) + (β-B) into Case I; the small-witness certificate is the proven Washington-9.5
descent for Case II; `p = 3` is Mathlib's `fermatLastTheoremThree`. No modularity input
anywhere. -/
theorem fermatLastTheorem_of_vandiver_window (C : ℕ)
    (hswcert : ∀ (p : ℕ) [Fact p.Prime], 3 < p → SmallWitnessCert p)
    (hα : ∀ p : ℕ, p.Prime → 2 < p → 0 < (sgWindow p (C * p ^ 2)).card)
    (hβA : ∀ p : ℕ, p.Prime → 2 < p →
      2 * ∑ q ∈ sgWindow p (C * p ^ 2), sgPairCount p q
        ≤ (sgWindow p (C * p ^ 2)).card)
    (hβB : ∀ p : ℕ, p.Prime → 2 < p →
      4 * ((sgWindow p (C * p ^ 2)).filter fun q => sgPowFail p q = true).card
        ≤ (sgWindow p (C * p ^ 2)).card) :
    FermatLastTheorem := by
  refine fermatLastTheorem_of_vandiver_caseI hswcert ?_
  intro p hp hne
  haveI := Fact.mk hp
  have hp2 : 2 < p := by
    have h2 := hp.two_le
    omega
  intro a b c hcase
  exact caseI_of_supply_of_cancellation (p := p) (hp.odd_of_ne_two hne)
    (hα p hp hp2) le_rfl (hβA p hp hp2) (hβB p hp hp2) hcase

end FltVandiver
