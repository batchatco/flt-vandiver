import FltVandiver.Prop818
import FltVandiver.QiBridgeProof
open CyclotomicNT

/-!
# Discharging `prop_8_18` and the `Q_i` bridge (irregular half)

`FltVandiver/Prop818.lean` proved the core `qi_pow_eq_one_of_isPth_power` (`Eᵢ = vᵖ ⟹ Q_iᵏ = 1`).
This file packages it as **`prop_8_18`** (now a THEOREM: irregular `i` + cert fires `⟹ Eᵢ ∉ E^p`) by
connecting `Eᵢ ∈ E^p` to the `vOf` class map (`vOf_eq_zero_iff`), and builds the bridge
**`qiVandiverBridge_all`** from it: when the certificate fires at *every* even index, each `Eᵢ ∉
    E^p`
follows from `prop_8_18` alone — needing **no** D-reg axiom.  (An earlier D-reg variant,
`qiVandiverBridge_proof`, tested only irregular indices and trusted `regularIndex_not_pth_power` for
the regular ones; it has been removed as superseded.)  The certificate's `t^{ℓ-1}=1` and `2 ∣ k`
clauses supply exactly Prop 8.18's validity hypotheses (`μ = tᵏ` a primitive `p`-th root). -/

namespace FltVandiver

open scoped NumberField
open NumberField NumberField.IsCMField Finset
open FltVandiver.QiCert

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] {ζ : K}

/-- **Washington Prop 8.18 (D-irr), now a THEOREM.** For ANY even index `i ∈ [2, p-3]` (irregularity
is NOT needed — that is only Washington's optimization), with the certificate's validity conditions
(`ℓ≡1 mod p`, `t` a unit `t^{ℓ-1}=1`, `tᵏ≠1`, `k` even), if the test fires (`Q_iᵏ≠1`) then `Eᵢ ∉
    E^p`.
Proof: contrapositive of `qi_pow_eq_one_of_isPth_power` (`Eᵢ=vᵖ ⟹ Q_iᵏ=1`); `Eᵢ ∈ E^p` comes from
`vOf⟨Eᵢ⟩ = 0` via `vOf_eq_zero_iff`. -/
theorem prop_8_18 (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (i : ℕ)
    (hiev : Even i) (hi2 : 2 ≤ i) (hip : i ≤ p - 3)
    {ℓ t : ℕ} [Fact ℓ.Prime] (hℓ : ℓ % p = 1) (ht1 : (t : ZMod ℓ) ^ (ℓ - 1) = 1)
    (htk : (t : ZMod ℓ) ^ ((ℓ - 1) / p) ≠ 1) (hke : 2 ∣ (ℓ - 1) / p)
    (hQ : qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1) :
    EigenNotPow hζ hp i := by
  have ht0 : (t : ZMod ℓ) ≠ 0 := by
    intro h
    rw [h, zero_pow (by have := (Fact.out : ℓ.Prime).two_le; omega)] at ht1
    exact zero_ne_one ht1
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓ htk ht0
  intro hzero
  apply hQ
  obtain ⟨v, hv⟩ := (vOf_eq_zero_iff _).mp hzero
  refine qi_pow_eq_one_of_isPth_power (hζ := hζ) (hμ := hμ) (i := i) (hp := hp) (hℓ := hℓ)
    (hkeven := hke) (hieven := hiev) (hi2 := hi2) (hip := hip) (hpow := ⟨(v : (𝓞 K)ˣ), ?_⟩)
  have hco := congrArg (fun x : realUnits K => (x : (𝓞 K)ˣ)) hv
  simpa using hco

end FltVandiver

namespace FltVandiver.QiCert

open FltVandiver NumberField

/-- The list of all even indices `[2, 4, …, p-3]`. -/
def evenIndices (p : ℕ) : List ℕ := (List.range ((p - 3) / 2)).map (fun j => 2 * (j + 1))

theorem mem_evenIndices {p : ℕ} (_hpodd : p % 2 = 1) {k : ℕ} (hk : k < (p - 3) / 2) :
    2 * (k + 1) ∈ evenIndices p :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

/-- **`qiVandiverBridge` testing ALL even indices — no D-reg axiom.**  If the `Q_i` certificate
    fires
for `evenIndices p` (every even `i ∈ [2,p-3]`), then `IsVandiverPrime p`.  Each `Eᵢ ∉ E^p` follows
directly from the now-proven `prop_8_18` (no irregularity, no per-character class-number input), so
this rests on NO Phase-D axiom — only Thm 8.2 + the p-rank bound.  Works whenever a single `(ℓ,t)`
makes every even `Q_iᵏ ≠ 1` (verified for `p = 37` at `(ℓ,t)=(149,2)`). -/
theorem qiVandiverBridge_all {p : ℕ} [hpri : Fact p.Prime] {ℓ t : ℕ} [Fact ℓ.Prime]
    (hcert : vandiverCert p ℓ t (evenIndices p) = true) :
    IsVandiverPrime p := by
  rcases eq_or_ne p 2 with rfl | hp
  · exact isVandiverPrime_two
  have hpri' : p.Prime := Fact.out
  have hp2 : 2 < p := lt_of_le_of_ne hpri'.two_le (Ne.symm hp)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpri'.odd_of_ne_two hp)
  haveI : NeZero p := ⟨hpri'.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  haveI : IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (CyclotomicField p ℚ) (S := {p})
      ⟨p, Set.mem_singleton p, hp2⟩
  set ζ : CyclotomicField p ℚ := IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  simp only [vandiverCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcert
  obtain ⟨⟨⟨⟨hℓ, htk⟩, ht1⟩, hke⟩, hQcert⟩ := hcert
  have hQall : ∀ i ∈ evenIndices p, qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1 :=
    fun i hi => of_decide_eq_true (List.all_eq_true.mp hQcert i hi)
  have hne : ∀ k : Fin ((p - 3) / 2), eigenFamily hζ hp k ≠ 0 := by
    intro k
    have hki : k.1 < (p - 3) / 2 := k.2
    have hiev : Even (2 * (k.1 + 1)) := ⟨k.1 + 1, by ring⟩
    have hi2 : 2 ≤ 2 * (k.1 + 1) := by omega
    have hip : 2 * (k.1 + 1) ≤ p - 3 := by omega
    change EigenNotPow hζ hp (2 * (k.1 + 1))
    exact prop_8_18 hζ hp _ hiev hi2 hip hℓ ht1 htk hke (hQall _ (mem_evenIndices hpodd hki))
  exact (hpri'.coprime_iff_not_dvd).mpr (vandiver_aux hζ hp hne)

end FltVandiver.QiCert
