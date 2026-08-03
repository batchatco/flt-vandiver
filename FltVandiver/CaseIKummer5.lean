import CyclotomicNT.CaseIKummer
import FltVandiver.MirimanoffSum5

/-!
# The `n = 5` Kummer log-derivative facts (bricks 2–4 of the `B_{p-5}` Case I route)

Siblings of the `n = 3` lemmas in `CyclotomicNT.CaseIKummer` / `KummerLogDeriv`:

* **Brick 2** — `not_dvd_four`, `not_dvd_five`: the coprimality side conditions
  `p-1 ∤ 4`, `p-1 ∤ 5` that `ell_eq_of_piRed_eq` needs at `n = 5` (mirror of `not_dvd_two/three`).
* **Brick 3** — `ell_five_geomUnit_ne_zero`: `ℓ₅(1−tX) ≠ 0` for `t ∉ {0,1,−1}` with `1+10t+t² ≠ 0`
  (mirror of `ell_three_geomUnit_ne_zero`), via `ell_geomUnit 5` + the S₄ nonvanishing (brick 1).
* **Brick 4** — `ell_five_eq_zero_of_conj_inv` / `ell_five_eq_zero_of_unit`: Kummer's unit lemma
  at `n = 5` (mirror of `ell_three_eq_zero_of_{conj_inv,unit}`), via the σ₋₁-trick and the fact
  that `u = ζᵐ·(conj-invariant)`.

Imports only; edits nothing.
-/

open Finset NumberField AddMonoidAlgebra IsCyclotomicExtension.Rat
open scoped Pointwise nonZeroDivisors

namespace CyclotomicNT.KummerLog

variable {p : ℕ} [hpri : Fact p.Prime]

/-! ### Brick 2: coprimality side conditions at `n = 5` -/

omit hpri in
theorem not_dvd_four (hp7 : 7 ≤ p) : ¬ (p - 1) ∣ 4 := fun h => by
  have := Nat.le_of_dvd (by norm_num) h
  omega

omit hpri in
theorem not_dvd_five (hp7 : 7 ≤ p) : ¬ (p - 1) ∣ 5 := fun h => by
  have := Nat.le_of_dvd (by norm_num) h
  omega

/-! ### Brick 3: nonvanishing of `ℓ₅` on the geometric unit -/

/-- **Nonvanishing at `n = 5`**: `ℓ₅(1−tX) ≠ 0` for `t ∉ {0, 1, −1}` with `1+10t+t² ≠ 0`.
The extra hypothesis is automatic when `6` is a non-residue mod `p` (e.g. `p = 2124679`). -/
theorem ell_five_geomUnit_ne_zero {t : ZMod p} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm1 : t ≠ -1)
    (hq : 1 + 10 * t + t ^ 2 ≠ 0) :
    ell 5 (geomUnit t h1) ≠ 0 := by
  rw [ell_geomUnit 5 (by omega)]
  intro h
  rcases mul_eq_zero.mp h with h | h
  · rw [neg_eq_zero, inv_eq_zero, sub_eq_zero] at h
    exact h1 h.symm
  · exact sum_quartic_mul_pow_ne_zero h0 h1 hm1 hq h

/-! ### Brick 4: Kummer's unit lemma at `n = 5`

Full CMField context (`k₀`, `ζ`, `hζ`) below; the unit-algebra middle of `ell_five_eq_zero_of_unit`
is identical to the `n = 3` version (index-independent), only the `ℓ`-lines change `3 → 5`. -/

variable {k₀ : Type*} [Field k₀] [NumberField k₀]
  [IsCyclotomicExtension {p} ℚ k₀] {ζ : k₀} (hζ : IsPrimitiveRoot ζ p)

/-- **Conj-invariant residues have `ℓ₅ = 0`** (the σ₋₁-trick, lift-free). -/
theorem ell_five_eq_zero_of_conj_inv (hp7 : 7 ≤ p) {w : 𝓞 k₀} {γ : (P p)ˣ}
    (hγ : piRed hζ ((γ : P p)) = Ideal.Quotient.mk _ w)
    (hw : ((galEquivZMod p k₀).symm (-1)) • w = w) :
    ell 5 γ = 0 := by
  have hπeq : piRed hζ ((sigmaU (-1) γ : (P p)ˣ) : P p) = piRed hζ ((γ : P p)) := by
    rw [sigmaU_val, piRed_sigma, hγ, galBar_mk, hw]
  have heq := ell_eq_of_piRed_eq hζ (by norm_num) (by
      rw [show (5 : ℕ) - 1 = 4 from rfl]
      exact not_dvd_four hp7) (not_dvd_five hp7) hπeq
  rw [ell_sigmaU 5 (by norm_num)] at heq
  have hcoe : (((-1 : (ZMod p)ˣ) : ZMod p)) ^ 5 = -1 := by
    rw [Units.val_neg, Units.val_one]
    ring
  rw [hcoe] at heq
  have h2 : (2 : ZMod p) * ell 5 γ = 0 := by linear_combination -heq
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h2' : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using h2'
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h h2ne
  · exact h

open NumberField.IsCMField in
/-- **`ℓ₅` vanishes on lifts of unit residues** (Kummer: `u = ζᵐ·(conj-invariant)`). -/
theorem ell_five_eq_zero_of_unit (hp7 : 7 ≤ p) (u : (𝓞 k₀)ˣ) {γ : (P p)ˣ}
    (hγ : piRed hζ ((γ : P p)) = Ideal.Quotient.mk _ ((u : 𝓞 k₀))) :
    ell 5 γ = 0 := by
  classical
  have hp2 : 2 < p := by omega
  haveI : NumberField.IsCMField k₀ := IsCyclotomicExtension.Rat.isCMField (S := {p}) (K := k₀) ⟨p,
      rfl, hp2⟩
  obtain ⟨m, hm⟩ := unit_inv_conj_is_root_of_unity hζ u hp2
  set w : (𝓞 k₀)ˣ := ((hζ.unit')⁻¹) ^ m * u with hw
  have hcu : unitsComplexConj k₀ u = ((hζ.unit' ^ m) ^ 2)⁻¹ * u := by
    have hm' : (hζ.unit' ^ m) ^ 2 = u * (unitsComplexConj k₀ u)⁻¹ := by
      rw [hm]; congr 2; exact Units.ext rfl
    rw [hm']
    group
  have hconjw : unitsComplexConj k₀ w = w := by
    rw [hw, map_mul, map_pow, map_inv, unitsComplexConj_unit' hζ hp2, hcu]
    group
  have hu_eq : u = (hζ.unit') ^ m * w := by
    rw [hw]
    group
  have hwnot : ((w : (𝓞 k₀)ˣ) : 𝓞 k₀)
      ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
    intro hmem
    exact (hζ.isPrime_one_sub_zeta).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem w.isUnit)
  obtain ⟨γw, hγw⟩ := exists_unit_lift hζ hwnot
  have hconjw' : ((galEquivZMod p k₀).symm (-1)) • ((w : (𝓞 k₀)ˣ) : 𝓞 k₀)
      = ((w : (𝓞 k₀)ˣ) : 𝓞 k₀) := by
    rw [galSymm_neg_one_smul hζ hp2,
      show ringOfIntegersComplexConj k₀ ((w : (𝓞 k₀)ˣ) : 𝓞 k₀)
        = ((unitsComplexConj k₀ w : (𝓞 k₀)ˣ) : 𝓞 k₀) from rfl, hconjw]
  have hℓw : ell 5 γw = 0 := ell_five_eq_zero_of_conj_inv hζ hp7 hγw hconjw'
  set δu := singleUnit (((m : ℕ) : ZMod p)) (1 : ZMod p) one_ne_zero with hδu
  have hπδ : piRed hζ ((δu : (P p)ˣ) : P p) = Ideal.Quotient.mk _ (hζ.toInteger ^ m) := by
    change piRed hζ (single (((m : ℕ) : ZMod p)) (1 : ZMod p)) = _
    rw [piRed_single, one_smul, ZMod.val_natCast, pow_val_mod (zetaBar_pow_p hζ), zetaBar,
      map_pow]
  have hpieq : piRed hζ ((δu * γw : (P p)ˣ) : P p) = piRed hζ ((γ : P p)) := by
    rw [Units.val_mul, map_mul, hπδ, hγw, hγ, ← map_mul]
    congr 1
    rw [hu_eq, Units.val_mul, ← unit'_val_eq_toInteger hζ]
    congr 1
  have heq := ell_eq_of_piRed_eq hζ (by norm_num) (by
      rw [show (5 : ℕ) - 1 = 4 from rfl]
      exact not_dvd_four hp7) (not_dvd_five hp7) hpieq
  rw [ell_mul, show ell 5 δu = 0 from ell_singleUnit 5 (by norm_num) _ _ _, hℓw,
    add_zero] at heq
  exact heq.symm

/-! ### Brick 5: the `η₅`-relation from a trivial weight-5 eigencomponent -/

open Ideal in
/-- If the weight-5 eigencomponent of `[I]` is trivial, then the `η₅`-twisted product of the
conjugates of `β` is a unit times a `p`-th power (mirror of `eta_three_relation`). -/
theorem eta_five_relation {β : 𝓞 k₀} (_hβ0 : β ≠ 0) {Iid : Ideal (𝓞 k₀)}
    (hI : Ideal.span {β} = Iid ^ p) (hIne : Iid ≠ 0)
    (htriv : eigenProj p 5 (ClassGroup.mk0
      ⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩) = 1) :
    ∃ (u : (𝓞 k₀)ˣ) (z : 𝓞 k₀),
      (∏ b : (ZMod p)ˣ, ((((galEquivZMod p k₀).symm b) • β : 𝓞 k₀))
          ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val)
        = (u : 𝓞 k₀) * z ^ p
      ∧ Ideal.span {z} = ∏ b : (ZMod p)ˣ,
          ((((galEquivZMod p k₀).symm b) • Iid : Ideal (𝓞 k₀)))
            ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val := by
  classical
  set Isub : (Ideal (𝓞 k₀))⁰ := ⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩ with hIsub
  -- the eigenprojection ideal is principal
  have hprin : Submodule.IsPrincipal (∏ a : (ZMod p)ˣ,
      ((((galEquivZMod p k₀).symm a)⁻¹ • Iid : Ideal (𝓞 k₀)))
        ^ (((a ^ 5 : (ZMod p)ˣ) : ZMod p)).val) := by
    have h1 : eigenProj p 5 (ClassGroup.mk0 Isub)
        = ClassGroup.mk0 (∏ a : (ZMod p)ˣ,
          (⟨((galEquivZMod p k₀).symm a)⁻¹ • Iid,
            smul_mem_nonZeroDivisors _ Isub⟩ : (Ideal (𝓞 k₀))⁰)
              ^ (((a ^ 5 : (ZMod p)ˣ) : ZMod p)).val) := by
      rw [eigenProj, map_prod]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [map_pow]
      congr 1
      exact classGroupGalAct_mk0 _ Isub
    rw [h1] at htriv
    have h2 := (ClassGroup.mk0_eq_one_iff (∏ a : (ZMod p)ˣ,
      (⟨((galEquivZMod p k₀).symm a)⁻¹ • Iid,
        smul_mem_nonZeroDivisors _ Isub⟩ : (Ideal (𝓞 k₀))⁰)
          ^ (((a ^ 5 : (ZMod p)ˣ) : ZMod p)).val).2).mp htriv
    have hcoe : ((∏ a : (ZMod p)ˣ,
        (⟨((galEquivZMod p k₀).symm a)⁻¹ • Iid,
          smul_mem_nonZeroDivisors _ Isub⟩ : (Ideal (𝓞 k₀))⁰)
            ^ (((a ^ 5 : (ZMod p)ˣ) : ZMod p)).val : (Ideal (𝓞 k₀))⁰) : Ideal (𝓞 k₀))
        = ∏ a : (ZMod p)ˣ, ((((galEquivZMod p k₀).symm a)⁻¹ • Iid : Ideal (𝓞 k₀)))
            ^ (((a ^ 5 : (ZMod p)ˣ) : ZMod p)).val := by
      push_cast
      rfl
    rwa [hcoe] at h2
  -- reindex `a := b⁻¹`
  have hreidx : (∏ a : (ZMod p)ˣ,
      ((((galEquivZMod p k₀).symm a)⁻¹ • Iid : Ideal (𝓞 k₀)))
        ^ (((a ^ 5 : (ZMod p)ˣ) : ZMod p)).val)
      = ∏ b : (ZMod p)ˣ, ((((galEquivZMod p k₀).symm b) • Iid : Ideal (𝓞 k₀)))
          ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val := by
    rw [← Equiv.prod_comp (Equiv.inv (ZMod p)ˣ) fun b =>
      ((((galEquivZMod p k₀).symm b) • Iid : Ideal (𝓞 k₀)))
        ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [show Equiv.inv (ZMod p)ˣ a = a⁻¹ from rfl, ← map_inv, inv_inv]
  rw [hreidx] at hprin
  obtain ⟨z, hz⟩ := hprin.principal
  rw [Ideal.submodule_span_eq] at hz
  have hpow : Ideal.span {z ^ p}
      = Ideal.span {(∏ b : (ZMod p)ˣ, ((((galEquivZMod p k₀).symm b) • β : 𝓞 k₀))
          ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val)} := by
    rw [← Ideal.span_singleton_pow, ← hz, ← Ideal.prod_span_singleton, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hsmulpow : (((galEquivZMod p k₀).symm b) • Iid : Ideal (𝓞 k₀)) ^ p
        = ((galEquivZMod p k₀).symm b) • (Iid ^ p) := by
      rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def, Ideal.map_pow]
    have hsmulspan : (((galEquivZMod p k₀).symm b) • (Ideal.span {β}) : Ideal (𝓞 k₀))
        = Ideal.span {(((galEquivZMod p k₀).symm b) • β : 𝓞 k₀)} := by
      rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
      rfl
    rw [← pow_mul, mul_comm, pow_mul, hsmulpow, ← hI, hsmulspan, Ideal.span_singleton_pow]
  rw [Ideal.span_singleton_eq_span_singleton] at hpow
  obtain ⟨u, hu⟩ := hpow
  exact ⟨u, z, by rw [← hu]; ring, hz.symm⟩

/-! ### Brick 6: the core dichotomy at `n = 5` -/

open Ideal in
include hζ in
/-- **The core dichotomy at `n = 5`** (mirror of `isIrregular_of_span_eq_pow`): a factorization
`(x+ζy) = Iᵖ` whose Mirimanoff ratio `t = −y/x` avoids `{0, 1, −1}` and the roots of `1+10t+t²`
(hypothesis `hq`) forces `p − 5` to be an irregular index.  No side condition on `6`: the caller
supplies a root-free ratio via `exists_good_ratio_5`. -/
theorem isIrregular_of_span_eq_pow_5 (hp7 : 7 ≤ p)
    {x y : ℤ} {Iid : Ideal (𝓞 k₀)}
    (hI : Ideal.span {((x : ℤ) : 𝓞 k₀) + hζ.toInteger * ((y : ℤ) : 𝓞 k₀)} = Iid ^ p)
    (hx : ((x : ℤ) : ZMod p) ≠ 0)
    (hsum : ((x : ℤ) : ZMod p) + ((y : ℤ) : ZMod p) ≠ 0)
    (ht0 : -((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹ ≠ 0)
    (ht1 : -((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹ ≠ 1)
    (htm1 : -((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹ ≠ -1)
    (hq : 1 + 10 * (-((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹)
        + (-((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹) ^ 2 ≠ 0) :
    QiCert.IsIrregularIndex p (p - 5) := by
  classical
  set β : 𝓞 k₀ := ((x : ℤ) : 𝓞 k₀) + hζ.toInteger * ((y : ℤ) : 𝓞 k₀) with hβ
  -- `β ∉ (ζ−1)` since `x + y ≢ 0 (mod p)`
  have hβp : β ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
    intro hmem
    have hxy : (((x + y : ℤ)) : 𝓞 k₀)
        ∈ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
      have hdecomp : (((x + y : ℤ)) : 𝓞 k₀)
          = β - ((y : ℤ) : 𝓞 k₀) * (hζ.unit' - 1 : 𝓞 k₀) := by
        rw [hβ, ← unit'_val_eq_toInteger hζ]
        push_cast
        ring
      rw [hdecomp]
      exact Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    have := intCast_mem_zeta_sub_one hζ hxy
    apply hsum
    have hcast : (((x + y : ℤ)) : ZMod p) = 0 := by
      rcases this with ⟨m, hm⟩
      rw [hm]
      push_cast
      rw [ZMod.natCast_self]
      ring
    push_cast at hcast
    linear_combination hcast
  have hβ0 : β ≠ 0 := fun h => hβp (h ▸ Ideal.zero_mem _)
  have hIne : Iid ≠ 0 := by
    intro h
    rw [h, zero_pow hpri.out.ne_zero] at hI
    exact hβ0 (Ideal.span_singleton_eq_bot.mp hI)
  by_cases htriv : eigenProj p 5 (ClassGroup.mk0
      ⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩) = 1
  case neg =>
    -- Herbrand fires
    have hclp : (ClassGroup.mk0
        (⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩ : (Ideal (𝓞 k₀))⁰)) ^ p = 1 := by
      rw [← map_pow]
      refine (ClassGroup.mk0_eq_one_iff
        ((⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩ : (Ideal (𝓞 k₀))⁰) ^ p).2).mpr ?_
      have hcoe : (((⟨Iid, mem_nonZeroDivisors_iff_ne_zero.mpr hIne⟩ : (Ideal (𝓞 k₀))⁰) ^ p :
          (Ideal (𝓞 k₀))⁰) : Ideal (𝓞 k₀)) = Iid ^ p := by
        push_cast
        rfl
      rw [hcoe, ← hI]
      exact ⟨⟨β, by rw [hβ, Ideal.submodule_span_eq]⟩⟩
    exact herbrand_eigenProj (by decide) (by norm_num) (by omega) hclp htriv
  case pos =>
    exfalso
    obtain ⟨u, z, hA, hzspan⟩ := eta_five_relation hβ0 hI hIne htriv
    -- `z ∉ (ζ−1)`: the prime-divisibility chase
    have hzp : z ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
      intro hmem
      have h𝔭ne : Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) ≠ ⊥ := by
        intro h
        have h1 := Ideal.span_singleton_eq_bot.mp h
        rw [sub_eq_zero, unit'_val_eq_toInteger hζ] at h1
        have h2 : ζ = 1 := by
          have hc := congrArg (algebraMap (𝓞 k₀) k₀) h1
          have ht : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
          rwa [ht, map_one] at hc
        exact (hζ.ne_one hpri.out.one_lt) h2
      have hprime : Prime (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))) :=
        Ideal.prime_of_isPrime h𝔭ne (hζ.isPrime_one_sub_zeta)
      have hdvd1 : Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) ∣ Ideal.span {z} := by
        rw [Ideal.dvd_iff_le]
        exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
      rw [hzspan] at hdvd1
      obtain ⟨b, _, hdvd2⟩ := hprime.exists_mem_finset_dvd hdvd1
      have hdvd3 := hprime.dvd_of_dvd_pow hdvd2
      obtain ⟨C, hC⟩ := hdvd3
      have hdvd4 : ((galEquivZMod p k₀).symm b)⁻¹
          • (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))) ∣ Iid := by
        refine ⟨((galEquivZMod p k₀).symm b)⁻¹ • C, ?_⟩
        have := congrArg (fun J => ((galEquivZMod p k₀).symm b)⁻¹ • J) hC
        simpa [smul_smul, smul_mul'] using this
      have h𝔭fix : ((galEquivZMod p k₀).symm b)⁻¹
          • (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)))
          = Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := by
        rw [← map_inv]
        rw [show ((galEquivZMod p k₀).symm b⁻¹)
            • (Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)))
            = Ideal.span {(((galEquivZMod p k₀).symm b⁻¹) • (hζ.unit' - 1 : 𝓞 k₀) : 𝓞 k₀)} from by
          rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
          rfl]
        have hpow : hζ.toInteger ^ p = 1 := by
          apply FaithfulSMul.algebraMap_injective (𝓞 k₀) k₀
          have ht : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
          rw [map_pow, map_one, ht]
          exact hζ.pow_eq_one
        have hsm : (((galEquivZMod p k₀).symm b⁻¹) • (hζ.unit' - 1 : 𝓞 k₀) : 𝓞 k₀)
            = hζ.toInteger ^ (((b⁻¹ : (ZMod p)ˣ) : ZMod p)).val - 1 := by
          rw [show (hζ.unit' - 1 : 𝓞 k₀) = hζ.toInteger - 1 from by
            rw [← unit'_val_eq_toInteger hζ], smul_sub]
          congr 1
          · have h := galEquivZMod_smul_of_pow_eq p k₀ ((galEquivZMod p k₀).symm b⁻¹) hpow
            rw [MulEquiv.apply_symm_apply] at h
            exact h
          · exact map_one (MulSemiringAction.toRingHom _ (𝓞 k₀) ((galEquivZMod p k₀).symm b⁻¹))
        rw [hsm, show Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀))
            = Ideal.span {(hζ.toInteger - 1 : 𝓞 k₀)} from by
          rw [← unit'_val_eq_toInteger hζ]]
        exact Ideal.span_singleton_eq_span_singleton.mpr
          (associated_sub_one_pow_sub_one hζ.toInteger_isPrimitiveRoot hpri.out.two_le
            (ZMod.val_coe_unit_coprime b⁻¹)).symm
      rw [h𝔭fix] at hdvd4
      have hdvd5 : Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) ∣ Ideal.span {β} := by
        rw [hI]
        exact dvd_pow hdvd4 hpri.out.ne_zero
      exact hβp (Ideal.le_of_dvd hdvd5 (Ideal.subset_span rfl))
    -- lifts of `u` and `z`
    have hup : ((u : (𝓞 k₀)ˣ) : 𝓞 k₀)
        ∉ Ideal.span ({(hζ.unit' - 1 : 𝓞 k₀)} : Set (𝓞 k₀)) := fun hmem =>
      (hζ.isPrime_one_sub_zeta).ne_top (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)
    obtain ⟨γu, hγu⟩ := exists_unit_lift hζ hup
    obtain ⟨γz, hγz⟩ := exists_unit_lift hζ hzp
    -- the base unit `V = x̄·(1−tX)`, of value `x̄ + ȳX`
    set t : ZMod p := -((y : ℤ) : ZMod p) * (((x : ℤ) : ZMod p))⁻¹ with hT
    set V : (P p)ˣ := singleUnit 0 (((x : ℤ) : ZMod p)) hx * geomUnit t ht1 with hV
    have hVval : ((V : (P p)ˣ) : P p)
        = single 0 (((x : ℤ) : ZMod p)) + single 1 (((y : ℤ) : ZMod p)) := by
      rw [hV, Units.val_mul]
      change (single (0 : ZMod p) (((x : ℤ) : ZMod p)) : P p) * (1 - single 1 t) = _
      rw [mul_sub, mul_one, single_mul_single, zero_add]
      have hxt : (((x : ℤ) : ZMod p)) * t = -(((y : ℤ) : ZMod p)) := by
        rw [hT]
        field_simp
      rw [hxt]
      have hneg : (single (1 : ZMod p) (-(((y : ℤ) : ZMod p))) : P p)
          = -single 1 (((y : ℤ) : ZMod p)) := by
        classical
        ext m
        change (single (1 : ZMod p) (-(((y : ℤ) : ZMod p))) : P p) m
            = -((single (1 : ZMod p) (((y : ℤ) : ZMod p)) : P p) m)
        rw [AddMonoidAlgebra.single_apply, AddMonoidAlgebra.single_apply]
        split_ifs <;> ring
      rw [hneg]
      ring
    -- `π` of the conjugates of `V` are the conjugates of `β`
    have hpow : hζ.toInteger ^ p = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 k₀) k₀
      have ht2 : algebraMap (𝓞 k₀) k₀ hζ.toInteger = ζ := hζ.coe_toInteger
      rw [map_pow, map_one, ht2]
      exact hζ.pow_eq_one
    have hsmul_int : ∀ (n : ℤ) (w : OmodP k₀ p),
        (((n : ℤ) : ZMod p)) • w = (((n : ℤ)) : OmodP k₀ p) * w := by
      intro n w
      rw [Algebra.smul_def]
      congr 1
      exact eq_intCast ((ZMod.castHom dvd_rfl (OmodP k₀ p)).comp (Int.castRingHom (ZMod p))) n
    have hπV : ∀ b : (ZMod p)ˣ,
        piRed hζ (sigma b ((V : (P p)ˣ) : P p))
          = Ideal.Quotient.mk _ ((((galEquivZMod p k₀).symm b) • β : 𝓞 k₀)) := by
      intro b
      rw [hVval, map_add, map_add, sigma_single, sigma_single, piRed_single, piRed_single,
        mul_zero, mul_one, ZMod.val_zero, pow_zero, hsmul_int, hsmul_int, mul_one]
      have hsm : (((galEquivZMod p k₀).symm b) • β : 𝓞 k₀)
          = ((x : ℤ) : 𝓞 k₀)
            + hζ.toInteger ^ (((b : (ZMod p)ˣ) : ZMod p)).val * ((y : ℤ) : 𝓞 k₀) := by
        rw [hβ, smul_add, smul_mul']
        have hx2 : (((galEquivZMod p k₀).symm b) • (((x : ℤ)) : 𝓞 k₀) : 𝓞 k₀)
            = (((x : ℤ)) : 𝓞 k₀) :=
          map_intCast (MulSemiringAction.toRingHom _ (𝓞 k₀) _) x
        have hy2 : (((galEquivZMod p k₀).symm b) • (((y : ℤ)) : 𝓞 k₀) : 𝓞 k₀)
            = (((y : ℤ)) : 𝓞 k₀) :=
          map_intCast (MulSemiringAction.toRingHom _ (𝓞 k₀) _) y
        have hz2 : (((galEquivZMod p k₀).symm b) • hζ.toInteger : 𝓞 k₀)
            = hζ.toInteger ^ (((b : (ZMod p)ˣ) : ZMod p)).val := by
          have h := galEquivZMod_smul_of_pow_eq p k₀ ((galEquivZMod p k₀).symm b) hpow
          rw [MulEquiv.apply_symm_apply] at h
          exact h
        rw [hx2, hy2, hz2]
      rw [hsm, map_add, map_mul, map_pow, map_intCast, map_intCast, zetaBar]
      ring
    -- the twisted product and its `π`-image
    set bigProd : (P p)ˣ := ∏ b : (ZMod p)ˣ,
      (sigmaU b V) ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val with hbigProd
    have hcoeProd : ((bigProd : (P p)ˣ) : P p)
        = ∏ b : (ZMod p)ˣ, (sigma b ((V : (P p)ˣ) : P p))
            ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val := by
      rw [hbigProd, show (((∏ b : (ZMod p)ˣ,
          (sigmaU b V) ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val) : (P p)ˣ) : P p)
          = ∏ b : (ZMod p)ˣ, (((sigmaU b V) ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val
              : (P p)ˣ) : P p) from map_prod (Units.coeHom (P p)) _ _]
      exact Finset.prod_congr rfl fun b _ => by
        rw [show (((sigmaU b V) ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val : (P p)ˣ) : P p)
            = ((sigmaU b V : (P p)ˣ) : P p) ^ (((b⁻¹ ^ 5 : (ZMod p)ˣ) : ZMod p)).val from
          Units.val_pow_eq_pow_val _ _, sigmaU_val]
    have hRHS : piRed hζ ((γu * γz ^ p : (P p)ˣ) : P p)
        = Ideal.Quotient.mk _ (((u : (𝓞 k₀)ˣ) : 𝓞 k₀) * z ^ p) := by
      rw [Units.val_mul, map_mul, show ((γz ^ p : (P p)ˣ) : P p) = ((γz : (P p)ˣ) : P p) ^ p from
        Units.val_pow_eq_pow_val _ _, map_pow, hγu, hγz, ← map_pow, ← map_mul]
    have hpiProd : piRed hζ ((bigProd : (P p)ˣ) : P p)
        = piRed hζ ((γu * γz ^ p : (P p)ˣ) : P p) := by
      rw [hcoeProd, map_prod, Finset.prod_congr rfl fun b _ => by
        rw [map_pow, hπV b, ← map_pow], ← map_prod, hA, hRHS]
    -- the `ℓ₅`-contradiction (`hq` folds to `1 + 10t + t² ≠ 0` under `set t`)
    have h3 := ell_eq_of_piRed_eq hζ (by norm_num) (by
        rw [show (5 : ℕ) - 1 = 4 from rfl]
        exact not_dvd_four hp7) (not_dvd_five hp7) hpiProd
    rw [hbigProd, ell_etaProd 5 (by norm_num) V] at h3
    have hru : ell 5 (γu * γz ^ p) = 0 := by
      rw [ell_mul, ell_pow_p, ell_five_eq_zero_of_unit hζ hp7 u hγu, add_zero]
    rw [hru, neg_eq_zero] at h3
    have hVell : ell 5 V = ell 5 (geomUnit t ht1) := by
      rw [hV, ell_mul, ell_singleUnit 5 (by norm_num), zero_add]
    rw [hVell] at h3
    exact ell_five_geomUnit_ne_zero ht0 ht1 htm1 hq h3

end CyclotomicNT.KummerLog

namespace CyclotomicNT

/-! ### Brick 7: Kummer's criterion at `n = 5` -/

open KummerLog IsCyclotomicExtension in
/-- **Kummer's criterion at `p − 5`**: if `p ∤ B_{p−5}` (i.e. `p` is not irregular at index `p−5`)
and `6` is a non-residue mod `p`, then the first case of FLT holds at `p` (mirror of
`caseI_of_not_irregular`). -/
theorem caseI_of_not_irregular_5 {p : ℕ} [hpri : Fact p.Prime] (hp7 : 7 ≤ p)
    (hirr : ¬ QiCert.IsIrregularIndex p (p - 5))
    {a b c : ℤ} (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬ ↑p ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p := by
  intro H
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hp5 : 5 ≤ p := by omega
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hζK : IsPrimitiveRoot (zeta p ℚ (CyclotomicField p ℚ)) p :=
    zeta_spec p ℚ (CyclotomicField p ℚ)
  have hpodd : Odd p := hpri.out.odd_of_ne_two (by omega)
  -- the ζ-membership for `exists_ideal`
  have hζmem : hζK.toInteger
      ∈ Polynomial.nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos]
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) hζK.toInteger
        = zeta p ℚ (CyclotomicField p ℚ) := hζK.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζK.pow_eq_one
  -- `p` divides none of `a, b, c`
  have hpa : ¬ (p : ℤ) ∣ a := fun h => caseI ((h.mul_right b).mul_right c)
  have hpb : ¬ (p : ℤ) ∣ b := fun h => caseI ((h.mul_left a).mul_right c)
  have hpc : ¬ (p : ℤ) ∣ c := fun h => caseI (h.mul_left (a * b))
  have haz : ((a : ZMod p)) ≠ 0 := fun h => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hbz : ((b : ZMod p)) ≠ 0 := fun h => hpb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp h)
  have hcz : ((c : ZMod p)) ≠ 0 := fun h => hpc ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h)
  -- the triple sums to zero mod `p`
  have hsum0 : ((a : ZMod p)) + ((b : ZMod p)) + (-((c : ZMod p))) = 0 := by
    have hH := congrArg (fun n : ℤ => ((n : ZMod p))) H
    push_cast at hH
    rw [ZMod.pow_card, ZMod.pow_card, ZMod.pow_card] at hH
    linear_combination hH
  obtain ⟨A, B, hA, hB, hAB, hmem, ht0, ht1, htm1, htq⟩ :=
    exists_good_ratio_5 hp7 haz hbz (neg_ne_zero.mpr hcz) hsum0
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- pair `(ā, b̄)`: integer pair `(x, y) := (b, a)`
    obtain ⟨Iid, hIid⟩ := FltRegular.exists_ideal hp5
      (show b ^ p + a ^ p = c ^ p by linarith) (gcd_triple_of_cover (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        rcases hw with rfl | rfl | rfl
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr (Or.inr rfl))) hgcd)
      (by
        intro h
        exact caseI (by
          have : b * a * c = a * b * c := by ring
          rwa [this] at h)) hζmem
    exact hirr (isIrregular_of_span_eq_pow_5 hζK hp7 (x := b) (y := a) hIid hB
      (by rw [add_comm]; exact hAB) ht0 ht1 htm1 htq)
  · -- pair `(b̄, −c̄)`: integer pair `(x, y) := (−c, b)`
    obtain ⟨Iid, hIid⟩ := FltRegular.exists_ideal hp5
      (show (-c) ^ p + b ^ p = (-a) ^ p by
        rw [hpodd.neg_pow, hpodd.neg_pow]
        linarith) (gcd_triple_of_cover (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        rcases hw with rfl | rfl | rfl
        · exact Or.inr (by right; right; rfl)
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inr (by left; rfl)) hgcd)
      (by
        intro h
        exact caseI (by
          have h2 : (-c) * b * (-a) = a * b * c := by ring
          rwa [h2] at h)) hζmem
    refine hirr (isIrregular_of_span_eq_pow_5 hζK hp7 (x := -c) (y := b) hIid ?_ ?_ ?_ ?_ ?_ ?_)
    · push_cast
      exact hB
    · push_cast
      rw [add_comm]
      exact hAB
    · push_cast
      exact ht0
    · push_cast
      exact ht1
    · push_cast
      exact htm1
    · push_cast
      exact htq
  · -- pair `(−c̄, ā)`: integer pair `(x, y) := (a, −c)`
    obtain ⟨Iid, hIid⟩ := FltRegular.exists_ideal hp5
      (show a ^ p + (-c) ^ p = (-b) ^ p by
        rw [hpodd.neg_pow, hpodd.neg_pow]
        linarith) (gcd_triple_of_cover (by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
        rcases hw with rfl | rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr (by right; right; rfl)
        · exact Or.inr (by right; left; rfl)) hgcd)
      (by
        intro h
        exact caseI (by
          have h2 : a * (-c) * (-b) = a * b * c := by ring
          rwa [h2] at h)) hζmem
    refine hirr (isIrregular_of_span_eq_pow_5 hζK hp7 (x := a) (y := -c) hIid hB ?_ ?_ ?_ ?_ ?_)
    · push_cast
      rw [add_comm]
      exact hAB
    · push_cast
      exact ht0
    · push_cast
      exact ht1
    · push_cast
      exact htm1
    · push_cast
      exact htq

end CyclotomicNT
