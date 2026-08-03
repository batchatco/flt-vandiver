import FltRegular.NumberTheory.Unramified
import FltRegular.NumberTheory.Hilbert94
import FltRegular.NumberTheory.KummersLemma.Field
import FltVandiver.Lemma92
import CyclotomicNT.PrimitiveRootUnit
import CyclotomicNT.UnramifiedDescent

/-!
# Washington Lemma 9.2, step 4 — descent of unramifiedness `M/K ⟹ L/K⁺`

In the two towers `K⁺ ⊆ L ⊆ M` and `K⁺ ⊆ K ⊆ M` (number fields, `[L:K⁺]=p` odd prime, `[K:K⁺]=2`),
if `M/K` is unramified then `L/K⁺` is unramified: for a prime `P_L` of `𝓞L` over `p` of `𝓞K⁺`,
`e(P_L|p) ∣ [L:K⁺]=p` and `e(P_L|p) ∣ e(P_M|p) = e(P_K|p)·e(P_M|P_K) = e(P_K|p)·1 ∣ 2`, so being
coprime-to-2-and-dividing-`p` it is `1`.
-/

open NumberField Ideal Polynomial

variable {Kp K L M : Type} [Field Kp] [Field K] [Field L] [Field M]
  [NumberField Kp] [NumberField K] [NumberField L] [NumberField M]
  [Algebra Kp K] [Algebra Kp L] [Algebra Kp M] [Algebra K M] [Algebra L M]
  [IsScalarTower Kp K M] [IsScalarTower Kp L M]

/-- **Step 4.** With the CM two-tower `K⁺ ⊆ L ⊆ M`, `K⁺ ⊆ K ⊆ M` (`[L:K⁺]=p` odd prime,
`[K:K⁺]=2`, both `L/K⁺` and `K/K⁺` Galois), `M/K` unramified forces `L/K⁺` unramified. -/
theorem isUnramified_of_cm_tower {p : ℕ} (hodd : Odd p)
    [IsGalois Kp L] [IsGalois Kp K]
    (hLrank : Module.finrank Kp L = p) (hKrank : Module.finrank Kp K = 2)
    [IsUnramified (𝓞 K) (𝓞 M)] :
    IsUnramified (𝓞 Kp) (𝓞 L) := by
  refine ⟨fun 𝔭 h𝔭 h𝔭_bot ↦ ?_⟩
  haveI h𝔭_max : 𝔭.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔭_bot h𝔭
  intro P hP
  haveI hP_prime : P.IsPrime := hP.1
  haveI hP_over : P.LiesOver 𝔭 := hP.2
  have hdvd_p : ramificationIdx 𝔭 P ∣ p := by
    rw [← hLrank]; exact ramificationIdx_dvd_finrank h𝔭_bot
  obtain ⟨P_M, hP_M⟩ := Classical.choice (nonempty_primesOver (S := 𝓞 M) P)
  haveI hPM_prime : P_M.IsPrime := hP_M.1
  haveI hPM_over : P_M.LiesOver P := hP_M.2
  haveI hPM_over_kp : LiesOver P_M 𝔭 := LiesOver.trans P_M P 𝔭
  haveI hPM_over_K : LiesOver P_M (P_M.under (𝓞 K)) := inferInstance
  haveI hPK_prime : (P_M.under (𝓞 K)).IsPrime := IsPrime.under (𝓞 K) P_M
  haveI hPK_over_kp : LiesOver (P_M.under (𝓞 K)) 𝔭 := LiesOver.tower_bot P_M (P_M.under (𝓞 K)) 𝔭
  have hPK_bot : P_M.under (𝓞 K) ≠ ⊥ := by
    intro h_bot
    apply h𝔭_bot
    have h_under : (P_M.under (𝓞 K)).under (𝓞 Kp) = 𝔭 := hPK_over_kp.over.symm
    rw [← h_under, h_bot]
    exact Ideal.comap_bot_of_injective (algebraMap (𝓞 Kp) (𝓞 K))
      (FaithfulSMul.algebraMap_injective _ _)
  haveI hPK_max : (P_M.under (𝓞 K)).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hPK_bot hPK_prime
  have hM_unram : ramificationIdx (P_M.under (𝓞 K)) P_M = 1 :=
    IsUnramified.isUnramifiedAt (P_M.under (𝓞 K)) hPK_bot P_M ⟨hPM_prime, hPM_over_K⟩
  have hdvd_M : ramificationIdx 𝔭 P ∣ ramificationIdx 𝔭 P_M := ramificationIdx_dvd_of_tower 𝔭 P P_M
  have h_tower_K : ramificationIdx 𝔭 P_M
      = ramificationIdx 𝔭 (P_M.under (𝓞 K)) * ramificationIdx (P_M.under (𝓞 K)) P_M :=
    ramificationIdx_algebra_tower' 𝔭 (P_M.under (𝓞 K)) P_M
  rw [hM_unram, mul_one] at h_tower_K
  have hdvd_2 : ramificationIdx 𝔭 (P_M.under (𝓞 K)) ∣ 2 := by
    rw [← hKrank]; exact ramificationIdx_dvd_finrank h𝔭_bot
  rw [← h_tower_K] at hdvd_2
  exact eq_one_of_dvd_two_of_dvd_odd hodd (dvd_trans hdvd_M hdvd_2) hdvd_p

/-! ## Lemma 9.2 for the cyclotomic field — the class-number consequence

Assembling everything: given the minus-part `α` and `M/K` unramified (Lemma 9.1), the fixed field
`L/K⁺` is an unramified cyclic degree-`p` extension, so flt-regular's Hilbert-94 black box gives
`p ∣ h⁺`. (`M/K` unramified is the remaining `α`-specific input, from `KummersLemma.isUnramified`.)
-/

/-- **Washington Lemma 9.2 (class-number form).** From minus-part Kummer data over `ℚ(ζ_p)` with
`M = ℚ(ζ_p)(α^{1/p})` unramified over `ℚ(ζ_p)`, the prime `p` divides the class number of the
maximal real subfield `ℚ(ζ_p)⁺` — contradicting Vandiver's conjecture. -/
theorem cyclotomic_p_dvd_classNumber {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    [IsCMField (CyclotomicField p ℚ)]
    {a : CyclotomicField p ℚ} [Fact (Irreducible (X ^ p - C a))] (ha : a ≠ 0)
    (hτa : NumberField.IsCMField.complexConj (CyclotomicField p ℚ) a = a⁻¹)
    (hunram : IsUnramified (𝓞 (CyclotomicField p ℚ)) (𝓞 (AdjoinRoot (X ^ p - C a)))) :
    p ∣ Fintype.card (ClassGroup (𝓞 (maximalRealSubfield (CyclotomicField p ℚ)))) := by
  have hfne : (X ^ p - C a : (CyclotomicField p ℚ)[X]) ≠ 0 :=
    (Fact.out (p := Irreducible (X ^ p - C a))).ne_zero
  -- warm the `Module (CyclotomicField p ℚ) (AdjoinRoot _)` instance (cold synth fails)
  -- see Lemma92.lean for the analysis
  letI : Module (CyclotomicField p ℚ) (AdjoinRoot (X ^ p - C a)) := Algebra.toModule
  haveI : Module.Finite (CyclotomicField p ℚ) (AdjoinRoot (X ^ p - C a)) :=
    (AdjoinRoot.powerBasis hfne).finite
  haveI : NumberField (AdjoinRoot (X ^ p - C a)) :=
    NumberField.of_module_finite (CyclotomicField p ℚ) (AdjoinRoot (X ^ p - C a))
  obtain ⟨L, hLgal, hLrank⟩ := cyclotomic_exists_isGalois_finrank_eq hp ha hτa
  haveI : IsGalois (maximalRealSubfield (CyclotomicField p ℚ)) L := hLgal
  haveI : IsUnramified (𝓞 (CyclotomicField p ℚ)) (𝓞 (AdjoinRoot (X ^ p - C a))) := hunram
  haveI : IsUnramified (𝓞 (maximalRealSubfield (CyclotomicField p ℚ))) (𝓞 L) :=
    isUnramified_of_cm_tower (Kp := maximalRealSubfield (CyclotomicField p ℚ))
      (K := CyclotomicField p ℚ) (L := L) (M := AdjoinRoot (X ^ p - C a))
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hLrank
      (Algebra.IsQuadraticExtension.finrank_eq_two _ (CyclotomicField p ℚ))
  haveI : IsCyclic (L ≃ₐ[maximalRealSubfield (CyclotomicField p ℚ)] L) :=
    isCyclic_aut_of_finrank_prime hLrank
  haveI : Algebra.Unramified (𝓞 (maximalRealSubfield (CyclotomicField p ℚ))) (𝓞 L) :=
    IsUnramified.toUnramified
  have hdvd := dvd_card_classGroup_of_unramified_isCyclic
    (K := maximalRealSubfield (CyclotomicField p ℚ)) (L := L)
    (by rw [hLrank]; exact Fact.out) (by rw [hLrank]; omega)
  rwa [hLrank] at hdvd

/-! ## Lemma 9.1 — discharging the unramifiedness hypothesis

For a unit `u ≡ 1 mod (1-ζ)ᵖ` of `𝓞 K` (`K = ℚ(ζ_p)`) that is not a `p`-th power, the Kummer
extension `M = AdjoinRoot (Xᵖ - C u)` is unramified over `K`. This is flt-regular's
`KummersLemma.isUnramified` applied to `M` (which IS the splitting field, since `ζ ∈ K`),
discharging the `hunram` input of `cyclotomic_p_dvd_classNumber`. -/

set_option maxHeartbeats 800000 in -- elaborates `𝓞`/`AdjoinRoot` instances (heavy whnf)
/-- **Lemma 9.1.** `M = K(α^{1/p})` is unramified over `K = ℚ(ζ_p)` for `α = u` a unit `≡ 1 mod
(1-ζ)ᵖ` and not a `p`-th power. -/
theorem kummer_isUnramified {p : ℕ} [hpri : Fact p.Prime] (hp : p ≠ 2) {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : (𝓞 K)ˣ) (hcong : (hζ.unit' - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ p ≠ u)
    [Fact (Irreducible (X ^ p - C (↑u : K)))] :
    IsUnramified (𝓞 K) (𝓞 (AdjoinRoot (X ^ p - C (↑u : K)))) := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : IsSplittingField K (AdjoinRoot (X ^ p - C (↑u : K))) (X ^ p - C (↑u : K)) :=
    isSplittingField_AdjoinRoot_X_pow_sub_C ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩
      (Fact.out (p := Irreducible (X ^ p - C (↑u : K))))
  have hfne : (X ^ p - C (↑u : K) : K[X]) ≠ 0 :=
    (Fact.out (p := Irreducible (X ^ p - C (↑u : K)))).ne_zero
  letI : Module K (AdjoinRoot (X ^ p - C (↑u : K))) := Algebra.toModule
  haveI : Module.Finite K (AdjoinRoot (X ^ p - C (↑u : K))) := (AdjoinRoot.powerBasis hfne).finite
  haveI : NumberField (AdjoinRoot (X ^ p - C (↑u : K))) :=
    NumberField.of_module_finite K (AdjoinRoot (X ^ p - C (↑u : K)))
  haveI := KummersLemma.isUnramified hp hζ u hcong hu (AdjoinRoot (X ^ p - C (↑u : K)))
  exact IsUnramified.of_unramified

set_option maxHeartbeats 800000 in -- elaborates `𝓞`/`AdjoinRoot` instances (heavy whnf)
/-- **Washington Lemma 9.2, applied to a minus-part UNIT — ⚠️ VACUOUS hypotheses.** Given a
minus-part unit `u` of `𝓞 ℚ(ζ_p)` (`complexConj u = u⁻¹`) that is `≡ 1 mod (1-ζ)ᵖ` and not a `p`-th
power, `p` divides the class number of `ℚ(ζ_p)⁺`. **The hypotheses cannot be jointly satisfied:** a
minus unit is a root of unity (via `unitsMulComplexConjInv` landing in torsion), and the only root
of unity `≡ 1 mod 𝔭ᵖ` is `1 = 1ᵖ` — contradicting "not a `p`-th power". So this implication is
vacuously true and provides no content. The genuine §9.1 descent uses the *element-level*
`cyclotomic_p_dvd_classNumber` (below, on a minus **element**, not a unit), which is non-vacuous. -/
theorem cyclotomic_p_dvd_classNumber_of_minus_unit {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (hcong : (hζ.unit' - 1 : 𝓞 (CyclotomicField p ℚ)) ^ p ∣ (↑u : 𝓞 (CyclotomicField p ℚ)) - 1)
    (hu : ∀ v : CyclotomicField p ℚ, v ^ p ≠ u)
    [Fact (Irreducible (X ^ p - C (↑u : CyclotomicField p ℚ)))]
    (hτu : NumberField.IsCMField.complexConj (CyclotomicField p ℚ) (↑u) = (↑u)⁻¹) :
    p ∣ Fintype.card (ClassGroup (𝓞 (maximalRealSubfield (CyclotomicField p ℚ)))) := by
  have ha : (↑u : CyclotomicField p ℚ) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ)) _)).mpr
      (Units.ne_zero u)
  exact cyclotomic_p_dvd_classNumber hp ha hτu (kummer_isUnramified (by omega) hζ u hcong hu)

/-! ## Kummer's Lemma for Vandiver primes — minus-unit form (⚠️ VACUOUS, see warning)

`kummersLemma_vandiver` below is the contrapositive of `cyclotomic_p_dvd_classNumber_of_minus_unit`:
"under `p ∤ h⁺`, a minus-part unit `≡ 1 mod (1-ζ)ᵖ` is a `p`-th power."

**⚠️ WARNING (do not rely on this as the Kummer's-Lemma content / as removing `refinedKummer`).**
Its hypotheses are *vacuously* satisfiable only by `u = 1`, so the statement is trivially true and
supplies **no** substantive content. Reason: in a CM field, a unit `u` with `complexConj u = u⁻¹`
is a root of unity — Mathlib's `NumberField.IsCMField.unitsMulComplexConjInv : (𝓞 K)ˣ →* torsion K`
sends `u ↦ u·(conj u)⁻¹ = u²`, landing in the torsion subgroup, so `u² ∈ W` ⟹ `u ∈ W`. The only
root of unity `≡ 1 mod 𝔭ᵖ` is `1` (`v_𝔭(ζ^j-1) = 1 < p` for `j ≠ 0`, and `-ζ^j-1` is a `𝔭`-unit).
Hence the minus-part Kummer's Lemma is a degenerate corner; it does **not** replace `refinedKummer`
(the genuine `p`-adic-`L` content concerns real/general units, not minus units).

The substantive tool is the *element-level* `cyclotomic_p_dvd_classNumber` (a minus **element**
`a : K`, `a ≠ 0`, `complexConj a = a⁻¹`), which is non-vacuous and is what Washington's actual §9.1
descent uses (applied to `(-ζ⁻¹)(x+ζy)/(x+ζ⁻¹y)`). -/

