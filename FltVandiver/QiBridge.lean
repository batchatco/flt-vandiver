import FltVandiver.QiCertificate
import CyclotomicNT.BernoulliMod
import CyclotomicNT.RegularPrimes
import FltVandiver.Prop818Bridge
open CyclotomicNT

-- `native_decide` is the certificate mechanism of this development: compiler-trusted
-- boolean evaluation behind kernel-checked soundness bridges (see the trust note in
-- the README). The linter ban is Mathlib-specific; here the usage is by design.
set_option linter.style.nativeDecide false

/-!
# The `Q_i` Vandiver bridge (Piece 2) — reduction to its classical core

**Piece 1** (`FltVandiver.QiCertificate`) gave the machine-checked computation
`vandiverCert 37 149 2 [32] = true`.  **`CyclotomicNT.BernoulliMod`** discharges the irregular-index
fact (`irregularIndices_37`, a *theorem* via a memoized Bernoulli `native_decide`).  **Piece 2** is
the classical theorem that turns the certificate into `IsVandiverPrime p` (Washington, *Cyclotomic
Fields*, Thm 8.14, 8.16; Prop 8.18; Cor 8.19) — **p-adic-L-free**.  Its core (Thm 8.14, the
cyclotomic-unit-index theorem `p ∣ h⁺ ⟺ some Eᵢ is a p-th power`) is absent from Mathlib and
flt-regular (the missing `[E:C] = h⁺` rung), so we formalize it ourselves as the **theorem**
`cyclotomic_unit_index_proof` (`CyclotomicNT.CyclotomicUnitIndexProof`), and the bridge it feeds is
the **theorem** `qiVandiverBridge_all` (`FltVandiver.Prop818Bridge`), routing through the proven
`prop_8_18` → `vandiver_aux`.

Result: `IsVandiverPrime 37` is a *theorem* (`isVandiverPrime_37`) resting only on the two
machine-checked computations (`vandiverCert_37`, `irregularIndices_37`), routed through the
classical bridge (Thm 8.14 + Prop 8.18, both formalized).
-/

namespace FltVandiver.QiCert

open FltVandiver

instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The `Q_i` certificate fires at **every** even index of `37` (not just the irregular `32`):
`vandiverCert 37 149 2 (evenIndices 37) = true`, machine-checked. -/
theorem vandiverCert_all_37 : vandiverCert 37 149 2 (evenIndices 37) = true := by native_decide

/-- **`IsVandiverPrime 37` is a theorem** — discharged via the machine-checked `Q_i` certificate
firing at all even indices (`vandiverCert_all_37`) and `qiVandiverBridge_all`.  Because the
certificate tests *every* even index, each `Eᵢ ∉ E^p` follows from the proven `prop_8_18` alone —
so this rests on **no** Phase-D axiom (no D-reg, no Bernoulli/irregular-index input).  Both
classical inputs — the Thm 8.2 index `[E:C]=h⁺` and the Dirichlet p-rank — are themselves proven
theorems, so the only trust input is the `native_decide` certificate computation. -/
theorem isVandiverPrime_37 : IsVandiverPrime 37 :=
  qiVandiverBridge_all vandiverCert_all_37

end FltVandiver.QiCert
