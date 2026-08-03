import FltVandiver.CaseIKummer5
import FltVandiver.CaseIBernoulli5

/-!
# The full `B_{p-5}` Case I route, assembled (unconditional in `6`)

Composes the fast certificate's soundness bridge (`CaseIBernoulli5.caseI_not_irregular_bern5`)
with Kummer's `n = 5` criterion (`CyclotomicNT.caseI_of_not_irregular_5`). With the three-ratio
lemma `exists_good_ratio_5` in place, there is **no `6`-non-residue side condition**: a
machine-checkable `caseIBern5Cert p = true` alone proves the first case of FLT at `p` for coprime
triples, at *every* prime regular at `p-5`.

Everything is a pure leaf — imports only, edits nothing, so building it triggers no 2124679
recompile.
-/

set_option linter.style.nativeDecide false

namespace FltVandiver.CaseIBernoulli5

/-- **The full `B_{p-5}` Case I route.** For a prime `p ≥ 7`, a nonzero fast residue
(`caseIBern5Cert p = true`, i.e. `p ∤ B_{p-5}`) proves the first case of FLT at `p` for coprime
triples — no side condition on `6`. -/
theorem caseI_of_bern5Cert (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p)
    (hcert : caseIBern5Cert p = true)
    {a b c : ℤ} (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (hnd : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p :=
  CyclotomicNT.caseI_of_not_irregular_5 hp7 (caseI_not_irregular_bern5 p hp7 hcert) hgcd hnd

/-! ### End-to-end demonstrations

The full pipeline — `native_decide` cert → soundness bridge → Kummer `n = 5` criterion → Case I —
now closes at **both** Wolstenholme primes, including `16843` where `6` is a quadratic residue (so
the earlier root-free shortcut did not apply). Both are regular at `p-5`. -/

example {a b c : ℤ} (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (hnd : ¬ (7 : ℤ) ∣ a * b * c) :
    a ^ 7 + b ^ 7 ≠ c ^ 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcert : caseIBern5Cert 7 = true := by native_decide
  exact caseI_of_bern5Cert 7 (by norm_num) hcert hgcd hnd

/-- **Case I of FLT for `p = 16843` via `B_{p-5}`, with no Sophie-Germain input.** `16843` is
regular at index `p-5`; `6` is a residue there, but `exists_good_ratio_5` handles that. -/
theorem caseI_16843 {a b c : ℤ} (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hnd : ¬ (16843 : ℤ) ∣ a * b * c) : a ^ 16843 + b ^ 16843 ≠ c ^ 16843 := by
  haveI : Fact (Nat.Prime 16843) := ⟨by norm_num⟩
  have hcert : caseIBern5Cert 16843 = true := by native_decide
  exact caseI_of_bern5Cert 16843 (by norm_num) hcert hgcd hnd

end FltVandiver.CaseIBernoulli5
