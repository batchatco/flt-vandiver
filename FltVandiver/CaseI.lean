import CyclotomicNT.RegularPrimes
open CyclotomicNT

/-!
# Case I of FLT: the hypothesis interface

**Case I is *not* a Vandiver weakening.** Unlike Case II, the ideal `I_ζ` from the
factorization of `(a + ζ b) = I_ζ^p` is *not* fixed by complex conjugation `j`: `j` sends the
`ζ`-factor `(a + ζ b)` to the `ζ̄`-factor `(a + ζ⁻¹ b)`, a different factor, so `[I_ζ]` lies in
the *minus* part `Cl(K)⁻`, which `p ∤ h⁺` does **not** kill (the plus-part argument used in
`CaseII` does not apply). The classical route to Case I from class-group input is
**Stickelberger's theorem** (which annihilates `Cl(K)⁻`) — see Washington Ch. 9 — and even that
route is per-prime at its irregularity step.

This file therefore exposes Case I as an explicit *hypothesis*, `CaseIHolds p`, discharged:

* **per-prime** by the Sophie Germain / Legendre auxiliary-prime certificate
  (`caseI_of_sgCert`, `SophieGermain.lean`) — e.g. `caseI_37` at `q = 149`;
* **for regular primes** by `FltRegular.caseI`;
* **uniformly in `p`** by no known theorem: whether every prime `p` admits a
  Legendre/Sophie-Germain auxiliary prime `q = 2hp + 1` with `q ∤ W_{2h}` is a
  long-open problem, stated impersonally by Ribenboim (*13 Lectures on
  Fermat's Last Theorem*, Lecture IV: "It is not known whether for every
  prime `p` there exists `h ≥ 1` such that `q = 2hp+1` is a prime and
  `q ∤ W_{2h}`; this is a difficult problem"); Dickson (1909) proved the
  per-`p` finiteness backdrop (GRH-conditional results reach only density-1
  in `p`, never all `p`).

The regularity-free plumbing (`exists_ideal`, `ex_fin_div`, `caseI_easier`, `may_assume`) of
`FltRegular.CaseI` is the toolbox these routes draw on.
-/

namespace FltVandiver

/-- **Case I of FLT at `p`, as a hypothesis:** no nonzero solutions of `a^p + b^p = c^p` with
`p ∤ abc`.  Discharged per-prime by `caseI_of_sgCert` (Sophie Germain certificate,
`SophieGermain.lean`) or, for regular `p`, by `FltRegular.caseI`.  No uniform-in-`p` discharge
is known (see the module docstring). -/
def CaseIHolds (p : ℕ) : Prop :=
  ∀ a b c : ℤ, ¬(p : ℤ) ∣ a * b * c → a ^ p + b ^ p ≠ c ^ p

end FltVandiver
