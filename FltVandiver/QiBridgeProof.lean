import CyclotomicNT.IndexReduction
import FltVandiver.QiCertificate
import CyclotomicNT.BernoulliMod
import CyclotomicNT.RegularPrimes
open CyclotomicNT

/-!
# The `EigenNotPow` predicate for the `Q_i` bridge

The Thm 8.14 chain (`vandiver_aux`, `FltVandiver/IndexReduction.lean`) proved: if **every**
    cyclotomic unit `Eᵢ`
(even `i ∈ [2,p-3]`) has nonzero class in `V = E/E^p` (i.e. no `Eᵢ` is a `p`-th power), then `p ∤
    h⁺`.

This file defines the predicate `EigenNotPow hζ hp i` (= "`Eᵢ ∉ E^p`") that the bridge feeds to
`vandiver_aux`.  The "all `Eᵢ ∉ E^p`" hypothesis is supplied — for *every* even `i` — by the
now-proven **`prop_8_18`** (Washington **Prop 8.18**: `Eᵢ ∈ E^p ⟺ Q_iᵏ ≡ 1 (mod ℓ)`) once the
certificate fires at every even index; see `qiVandiverBridge_all` (`Prop818Bridge.lean`).  This
    route
is **p-adic-L-free** and uses **no** D-reg axiom (the earlier `regularIndex_not_pth_power` variant,
which trusted regularity for the regular indices, has been removed as superseded). -/

namespace FltVandiver

open scoped NumberField
open NumberField NumberField.IsCMField Finset
open FltVandiver.QiCert

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

/-- `Eᵢ` is **not** a `p`-th power: its class in `V = E/E^p` is nonzero.  By `vOf_eq_zero_iff`,
`EigenNotPow hζ hp i ↔ ¬ ∃ v, Eᵢ = vᵖ`.  Note `eigenFamily hζ hp k` is `vOf` of `E_{2(k+1)}`, so
`eigenFamily hζ hp k ≠ 0` is definitionally `EigenNotPow hζ hp (2*(k+1))`. -/
abbrev EigenNotPow (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (i : ℕ) : Prop :=
  (vOf ⟨eigenCyclotomicUnit hζ i, eigenCyclotomicUnit_mem_realUnits hζ hp i⟩ :
    ModN (Additive (realUnits K)) p) ≠ 0

end FltVandiver
