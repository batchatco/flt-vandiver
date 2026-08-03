import CyclotomicNT.CyclotomicUnitGroup
import FltVandiver.QiCertificate
import CyclotomicNT.PowerSumZMod
open CyclotomicNT

/-!
# Discharging `prop_8_18` (Washington Prop 8.18, the easy/certificate direction) — foundation

Goal: `Eᵢ ∈ E^p ⟹ Q_iᵏ ≡ 1 (mod ℓ)` (contrapositive of the certificate's use).  **No Gauss/Jacobi
sums.**  The argument:

1. `μ := (t : ZMod ℓ)ᵏ` (`k = (ℓ−1)/p`) is a primitive `p`-th root of unity (this file).
2. The reduction ring hom `φ : 𝓞 K →ₐ[ℤ] ZMod ℓ` with `φ(ζ) = μ`, built from the integral power
    basis
   and `μ` being a root of `cyclotomic p` (this file).
3. `φ(Eᵢ) = μ^A · S` with `S = ∏ₐ (∑_{j<a} μʲ)^{a^{p−1−i}}` (exponent algebra — next).
4. `φ(Eᵢ)·(μ−1)^{d'} = μ^A · t^{k·d_i/2} · Q_i`, then raise to `k`: both correction terms die
    because
   `p ∣ d'` (`half_sum_pow_eq_zero`), giving `φ(Eᵢ)ᵏ = Q_iᵏ`.
5. `Eᵢ = vᵖ ⟹ φ(Eᵢ)ᵏ = φ(v)^{ℓ−1} = 1` (Fermat) ⟹ `Q_iᵏ = 1`.

This file establishes steps 1–2. -/

namespace FltVandiver

open scoped NumberField
open NumberField Polynomial

variable {p : ℕ} [hpri : Fact p.Prime] {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime]

/-- The reduced root `μ = tᵏ ∈ ZMod ℓ`, `k = (ℓ−1)/p`. -/
noncomputable def redRoot (p ℓ t : ℕ) : ZMod ℓ := (t : ZMod ℓ) ^ ((ℓ - 1) / p)

section PrimRoot

/-- If `μ := tᵏ ≠ 1` and `ℓ ≡ 1 mod p`, then `μ` is a primitive `p`-th root of unity in `ZMod ℓ`.
(`μᵖ = t^{ℓ−1} = 1` by Fermat since `t ≢ 0`, and `μ ≠ 1`, `p` prime ⟹ order exactly `p`.) -/
theorem isPrimitiveRoot_redRoot (hℓ : ℓ % p = 1) (ht : redRoot p ℓ t ≠ 1)
    (ht0 : (t : ZMod ℓ) ≠ 0) : IsPrimitiveRoot (redRoot p ℓ t) p := by
  have hpdvd : p ∣ ℓ - 1 := by
    have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hpri.out.one_lt
    have hmod : (1 : ℕ) ≡ ℓ [MOD p] := by unfold Nat.ModEq; rw [h1, hℓ]
    exact (Nat.modEq_iff_dvd' (by have := hℓpri.out.two_le; omega)).mp hmod
  have hpow : redRoot p ℓ t ^ p = 1 := by
    rw [redRoot, ← pow_mul, Nat.div_mul_cancel hpdvd]
    exact ZMod.pow_card_sub_one_eq_one ht0
  have hord : orderOf (redRoot p ℓ t) = p := orderOf_eq_prime hpow ht
  have := IsPrimitiveRoot.orderOf (redRoot p ℓ t)
  rwa [hord] at this
end PrimRoot

section Hom
variable {K : Type*} [Field K] [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] {ζ : K}

omit [NumberField K] in
/-- The minimal polynomial of the integral primitive root is the `p`-th cyclotomic polynomial. -/
theorem minpoly_toInteger (hζ : IsPrimitiveRoot ζ p) :
    minpoly ℤ (hζ.integralPowerBasis.gen) = cyclotomic p ℤ := by
  rw [hζ.integralPowerBasis_gen]
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hcoe : (algebraMap (𝓞 K) K) hζ.toInteger = ζ := hζ.coe_toInteger
  rw [← minpoly.algebraMap_eq hinj hζ.toInteger, hcoe,
    ← cyclotomic_eq_minpoly hζ hpri.out.pos]

/-- The reduction algebra hom `φ : 𝓞 K →ₐ[ℤ] ZMod ℓ` with `φ(ζ) = μ = tᵏ`, built from the integral
power basis and the fact that `μ` is a root of `cyclotomic p`. -/
noncomputable def redHom (hζ : IsPrimitiveRoot ζ p) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) :
    𝓞 K →ₐ[ℤ] ZMod ℓ :=
  hζ.integralPowerBasis.lift (redRoot p ℓ t) <| by
    rw [minpoly_toInteger hζ]
    simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def, map_cyclotomic]
      using hμ.isRoot_cyclotomic hpri.out.pos

omit [NumberField K] in
@[simp] theorem redHom_zeta (hζ : IsPrimitiveRoot ζ p)
    (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) :
    redHom hζ hμ hζ.toInteger = redRoot p ℓ t := by
  rw [redHom, ← hζ.integralPowerBasis_gen, PowerBasis.lift_gen]

variable (hζ : IsPrimitiveRoot ζ p) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)

/-- Unit-level reduction `(𝓞 K)ˣ →* (ZMod ℓ)ˣ` induced by `φ`. -/
noncomputable def redUnit : (𝓞 K)ˣ →* (ZMod ℓ)ˣ :=
  Units.map (redHom hζ hμ).toRingHom.toMonoidHom

omit [NumberField K] in
theorem coe_redUnit (u : (𝓞 K)ˣ) :
    ((redUnit hζ hμ u : (ZMod ℓ)ˣ) : ZMod ℓ) = redHom hζ hμ (u : 𝓞 K) := by
  rw [redUnit, Units.coe_map]; rfl

omit [NumberField K] in
@[simp] theorem redUnit_zetaUnit_val :
    ((redUnit hζ hμ (zetaUnit hζ) : (ZMod ℓ)ˣ) : ZMod ℓ) = redRoot p ℓ t := by
  rw [coe_redUnit, show (zetaUnit hζ : 𝓞 K) = hζ.toInteger from by rw [zetaUnit, IsUnit.unit_spec],
    redHom_zeta]

omit [NumberField K] in
/-- `φ(cyclotomicUnit a) = ∑_{j<a} μʲ` (image of the geometric sum). -/
theorem redHom_cyclotomicUnit_val (a : ℕ) (ha : a.Coprime p) :
    redHom hζ hμ (cyclotomicUnit hζ.toInteger_isPrimitiveRoot hpri.out.two_le ha : 𝓞 K)
      = ∑ j ∈ Finset.range a, (redRoot p ℓ t) ^ j := by
  rw [coe_cyclotomicUnit, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_pow, redHom_zeta]

/-- `∏ g^(f a) = g^(∑ f a)` for a fixed base in a commutative group. -/
theorem prod_zpow_const {G ι : Type*} [CommGroup G] (s : Finset ι) (g : G)
    (f : ι → ℤ) : ∏ a ∈ s, g ^ (f a) = g ^ (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← zpow_add]

/-- The total `ζ`-prefactor exponent of `Eᵢ`: `A = ∑ₐ (1-a)·((p+1)/2)·a^{p-1-i}`. -/
def eigenPrefExp (p i : ℕ) : ℤ :=
  ∑ a ∈ (Finset.Icc 1 ((p - 1) / 2)).attach,
    (1 - (a.1 : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ) * ((a.1 ^ (p - 1 - i) : ℕ) : ℤ)

/-- The common geometric-sum product `S = ∏ₐ (∑_{j<a} μʲ)^{a^{p-1-i}}` in `ZMod ℓ`. -/
noncomputable def geomProd (p ℓ t i : ℕ) : ZMod ℓ :=
  ∏ a ∈ (Finset.Icc 1 ((p - 1) / 2)).attach,
    (∑ j ∈ Finset.range a.1, (redRoot p ℓ t) ^ j) ^ (a.1 ^ (p - 1 - i))

omit [NumberField K] in
/-- **`φ(Eᵢ) = μ^A · S`** — the cyclotomic-unit image collapses to a `ζ`-prefactor times the common
geometric-sum product. -/
theorem redHom_eigen_eq (i : ℕ) :
    redHom hζ hμ (eigenCyclotomicUnit hζ i : 𝓞 K)
      = (redRoot p ℓ t) ^ (eigenPrefExp p i) * geomProd p ℓ t i := by
  -- work at the unit level to handle the negative ζ-exponents cleanly
  have hu : redUnit hζ hμ (eigenCyclotomicUnit hζ i)
      = (redUnit hζ hμ (zetaUnit hζ)) ^ (eigenPrefExp p i)
        * ∏ a ∈ (Finset.Icc 1 ((p - 1) / 2)).attach,
            (redUnit hζ hμ
              (cyclotomicUnit hζ.toInteger_isPrimitiveRoot hpri.out.two_le
                (coprime_of_mem_Icc a.2))) ^ (a.1 ^ (p - 1 - i)) := by
    have hE : eigenCyclotomicUnit hζ i
        = ∏ a ∈ (Finset.Icc 1 ((p - 1) / 2)).attach,
            realCyclotomicUnit hζ a.1 (coprime_of_mem_Icc a.2) ^ (a.1 ^ (p - 1 - i)) := rfl
    rw [hE, map_prod, eigenPrefExp, ← prod_zpow_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_pow, realCyclotomicUnit, map_mul, map_zpow, mul_pow, ← zpow_natCast _ (a.1 ^ (p - 1 -
        i)),
      ← zpow_mul]
  -- push to values in ZMod ℓ
  rw [← coe_redUnit hζ hμ (eigenCyclotomicUnit hζ i), hu, Units.val_mul,
    Units.val_zpow_eq_zpow_val, redUnit_zetaUnit_val, geomProd, ← Units.coeHom_apply, map_prod]
  refine congrArg _ (Finset.prod_congr rfl fun a _ => ?_)
  rw [Units.coeHom_apply, Units.val_pow_eq_pow_val, coe_redUnit, redHom_cyclotomicUnit_val]

end Hom

section QiSide
open FltVandiver.QiCert
variable (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
include hμ

/-- `t ≢ 0 mod ℓ`, from `μ = tᵏ` being a primitive root (so `μ ≠ 0`). -/
theorem redRoot_base_ne_zero : (t : ZMod ℓ) ≠ 0 := by
  have hμ0 : redRoot p ℓ t ≠ 0 := by
    intro h
    have h1 := hμ.pow_eq_one
    rw [h, zero_pow hpri.out.pos.ne'] at h1
    exact zero_ne_one h1
  have hk0 : (ℓ - 1) / p ≠ 0 := fun h =>
    hμ.ne_one hpri.out.one_lt (by rw [redRoot, h, pow_zero])
  intro h
  exact hμ0 (by rw [redRoot, h, zero_pow hk0])

/-- The exponent-sum `d' = ∑_{a=1}^{(p-1)/2} a^{p-1-i}`. -/
def expSum (p i : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), a ^ (p - 1 - i)

/-- **`Q_i · t^{k·d_i/2} = S · (μ-1)^{d'}`** — clearing the inverse prefactor, the `Q_i` product
factors through the same geometric-sum product `S` via `μᵇ−1 = (∑_{j<b} μʲ)(μ−1)`. -/
theorem qi_mul_eq (i : ℕ) :
    qi p i ℓ t * (t : ZMod ℓ) ^ ((ℓ - 1) / p * dVal p i / 2)
      = geomProd p ℓ t i * (redRoot p ℓ t - 1) ^ expSum p i := by
  have ht0 := redRoot_base_ne_zero hμ
  simp only [qi]
  rw [mul_right_comm, ← mul_pow, inv_mul_cancel₀ ht0, one_pow, one_mul]
  -- now: ∏_b (t^(k*b)-1)^e_b = geomProd * (μ-1)^d'
  rw [geomProd, Finset.prod_attach (Finset.Icc 1 ((p - 1) / 2))
        (fun b => (∑ j ∈ Finset.range b, (redRoot p ℓ t) ^ j) ^ (b ^ (p - 1 - i))),
    expSum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [show (t : ZMod ℓ) ^ ((ℓ - 1) / p * b) = redRoot p ℓ t ^ b by rw [redRoot, ← pow_mul],
    ← geom_sum_mul (redRoot p ℓ t) b, mul_pow]

omit hμ in
omit hpri in
/-- `eigenPrefExp = (p+1)/2 · (d' − d_i)` — the total `ζ`-exponent in closed form. -/
theorem eigenPrefExp_eq (i : ℕ) (hip : i ≤ p - 1) :
    eigenPrefExp p i = (((p + 1) / 2 : ℕ) : ℤ) * ((expSum p i : ℤ) - (dVal p i : ℤ)) := by
  rw [eigenPrefExp, Finset.sum_attach (Finset.Icc 1 ((p - 1) / 2))
      (fun a => (1 - (a : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ) * ((a ^ (p - 1 - i) : ℕ) : ℤ)),
    expSum, dVal]
  push_cast
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_Icc] at ha
  have hsucc : (a : ℤ) ^ (p - i) = (a : ℤ) ^ (p - 1 - i) * a := by
    rw [← pow_succ]; congr 1; omega
  rw [hsucc]; ring

omit hμ in
/-- `p ∣ d'` (the exponent sum), since `d' = ∑ a^{p-1-i}` with `p-1-i` even —
    `half_sum_pow_eq_zero`. -/
theorem p_dvd_expSum (i : ℕ) (hp : p ≠ 2) (hieven : Even i) (hi2 : 2 ≤ i) (hip : i ≤ p - 3) :
    p ∣ expSum p i := by
  have heven : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hpri.out.odd_of_ne_two hp; exact ⟨k, by omega⟩
  have h0 : ((expSum p i : ℕ) : ZMod p) = 0 := by
    rw [expSum]; push_cast
    exact half_sum_pow_eq_zero p hp (p - 1 - i) (by omega) (by omega)
      ((Nat.even_sub (by omega)).mpr (iff_of_true heven hieven))
  exact (ZMod.natCast_eq_zero_iff _ _).mp h0

section Final
open FltVandiver.QiCert
variable {K : Type*} [Field K] [CharZero K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] {ζ : K}
variable (hζ : IsPrimitiveRoot ζ p)
include hζ hμ

omit [NumberField K] in
/-- **`φ(Eᵢ)ᵏ = Q_iᵏ`** in `ZMod ℓ` — the load-bearing identity.  From `φ(Eᵢ)·(μ-1)^{d'} =
μ^A·t^{k d_i/2}·Q_i`, raising to `k = (ℓ−1)/p` kills both correction terms because `p ∣ d'`:
`(μ-1)^{d'k}=1` (Fermat) and `μ^{Ak}·t^{k²d_i/2}=μ^M=1` (`p ∣ M`). -/
theorem redHom_eigen_pow_eq_Qi_pow (i : ℕ) (hp : p ≠ 2) (hℓ : ℓ % p = 1)
    (hkeven : 2 ∣ (ℓ - 1) / p) (hieven : Even i) (hi2 : 2 ≤ i) (hip : i ≤ p - 3) :
    redHom hζ hμ (eigenCyclotomicUnit hζ i : 𝓞 K) ^ ((ℓ - 1) / p) = qi p i ℓ t ^ ((ℓ - 1) / p) := by
  have hμ0 : redRoot p ℓ t ≠ 0 := by
    intro h; have h1 := hμ.pow_eq_one
    rw [h, zero_pow hpri.out.pos.ne'] at h1; exact zero_ne_one h1
  have hpd' : p ∣ expSum p i := p_dvd_expSum i hp hieven hi2 hip
  have hμne1 : redRoot p ℓ t ≠ 1 := hμ.ne_one hpri.out.one_lt
  have hpk : p * ((ℓ - 1) / p) = ℓ - 1 := by
    have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hpri.out.one_lt
    have hmod : (1 : ℕ) ≡ ℓ [MOD p] := by unfold Nat.ModEq; rw [h1, hℓ]
    rw [Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' (by have := hℓpri.out.two_le; omega)).mp hmod)]
  -- the key combined identity: φ(Eᵢ)·(μ-1)^{d'} = μ^A · t^{k d_i/2} · Q_i
  have hstar : redHom hζ hμ (eigenCyclotomicUnit hζ i : 𝓞 K) * (redRoot p ℓ t - 1) ^ expSum p i
      = redRoot p ℓ t ^ eigenPrefExp p i
        * (t : ZMod ℓ) ^ ((ℓ - 1) / p * dVal p i / 2) * qi p i ℓ t := by
    rw [redHom_eigen_eq, show redRoot p ℓ t ^ eigenPrefExp p i * geomProd p ℓ t i
        * (redRoot p ℓ t - 1) ^ expSum p i
        = redRoot p ℓ t ^ eigenPrefExp p i
          * (geomProd p ℓ t i * (redRoot p ℓ t - 1) ^ expSum p i) by ring,
      ← qi_mul_eq hμ i]; ring
  -- F1: (μ-1)^{d'·k} = 1, since p ∣ d' so d'·k is a multiple of ℓ-1
  have hF1 : (redRoot p ℓ t - 1) ^ (expSum p i * ((ℓ - 1) / p)) = 1 := by
    obtain ⟨c, hc⟩ := hpd'
    rw [hc, show p * c * ((ℓ - 1) / p) = (ℓ - 1) * c by rw [mul_right_comm, hpk], pow_mul,
      ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr hμne1), one_pow]
  -- t^{(k d_i/2)·k} = μ^{k d_i/2}
  have htmk : ((t : ZMod ℓ) ^ ((ℓ - 1) / p * dVal p i / 2)) ^ ((ℓ - 1) / p)
      = redRoot p ℓ t ^ (((ℓ - 1) / p * dVal p i / 2 : ℕ) : ℤ) := by
    rw [redRoot, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm ((ℓ - 1) / p * dVal p i / 2)]
  -- F2: μ^{A·k + k d_i/2} = 1, since p ∣ d' ⟹ p ∣ M
  have hM : redRoot p ℓ t ^ (eigenPrefExp p i * (((ℓ - 1) / p : ℕ) : ℤ)
        + (((ℓ - 1) / p * dVal p i / 2 : ℕ) : ℤ)) = 1 := by
    rw [hμ.zpow_eq_one_iff_dvd]
    obtain ⟨k', hk'⟩ := hkeven
    obtain ⟨c, hc⟩ := hpd'
    have hm : (ℓ - 1) / p * dVal p i / 2 = k' * dVal p i := by
      rw [hk', mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    have h2z : (2 : ℤ) * (((p + 1) / 2 : ℕ) : ℤ) = (p : ℤ) + 1 := by
      have : 2 * ((p + 1) / 2) = p + 1 := by obtain ⟨j, hj⟩ := hpri.out.odd_of_ne_two hp; omega
      exact_mod_cast this
    have hcz : (expSum p i : ℤ) = (p : ℤ) * (c : ℤ) := by exact_mod_cast hc
    rw [eigenPrefExp_eq i (by omega), hm, hk']
    refine ⟨(k' : ℤ) * (((p : ℤ) + 1) * (c : ℤ) - (dVal p i : ℤ)), ?_⟩
    simp only [Nat.cast_mul, Nat.cast_ofNat, hcz]
    linear_combination ((k' : ℤ) * ((p : ℤ) * (c : ℤ) - (dVal p i : ℤ))) * h2z
  calc redHom hζ hμ (eigenCyclotomicUnit hζ i : 𝓞 K) ^ ((ℓ - 1) / p)
      = redHom hζ hμ (eigenCyclotomicUnit hζ i : 𝓞 K) ^ ((ℓ - 1) / p)
          * (redRoot p ℓ t - 1) ^ (expSum p i * ((ℓ - 1) / p)) := by rw [hF1, mul_one]
    _ = (redHom hζ hμ (eigenCyclotomicUnit hζ i : 𝓞 K) * (redRoot p ℓ t - 1) ^ expSum p i)
          ^ ((ℓ - 1) / p) := by rw [mul_pow, ← pow_mul]
    _ = (redRoot p ℓ t ^ eigenPrefExp p i * (t : ZMod ℓ) ^ ((ℓ - 1) / p * dVal p i / 2)
          * qi p i ℓ t) ^ ((ℓ - 1) / p) := by rw [hstar]
    _ = redRoot p ℓ t ^ (eigenPrefExp p i * (((ℓ - 1) / p : ℕ) : ℤ)
          + (((ℓ - 1) / p * dVal p i / 2 : ℕ) : ℤ)) * qi p i ℓ t ^ ((ℓ - 1) / p) := by
        rw [mul_pow, mul_pow, ← zpow_natCast (redRoot p ℓ t ^ eigenPrefExp p i) ((ℓ - 1) / p),
          ← zpow_mul, htmk, ← zpow_add₀ hμ0]
    _ = qi p i ℓ t ^ ((ℓ - 1) / p) := by rw [hM, one_mul]

omit [NumberField K] in
/-- **Prop 8.18, easy direction (core).** If `Eᵢ` is a `p`-th power of a unit, then `Q_iᵏ ≡ 1`.
A `p`-th power maps to a `p`-th-power residue, so `φ(Eᵢ)ᵏ = φ(v)^{ℓ-1} = 1` (Fermat); combined with
`φ(Eᵢ)ᵏ = Q_iᵏ` this gives `Q_iᵏ = 1`. -/
theorem qi_pow_eq_one_of_isPth_power (i : ℕ) (hp : p ≠ 2) (hℓ : ℓ % p = 1)
    (hkeven : 2 ∣ (ℓ - 1) / p) (hieven : Even i) (hi2 : 2 ≤ i) (hip : i ≤ p - 3)
    (hpow : ∃ v : (𝓞 K)ˣ, eigenCyclotomicUnit hζ i = v ^ p) :
    qi p i ℓ t ^ ((ℓ - 1) / p) = 1 := by
  obtain ⟨v, hv⟩ := hpow
  have hpk : p * ((ℓ - 1) / p) = ℓ - 1 := by
    have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hpri.out.one_lt
    have hmod : (1 : ℕ) ≡ ℓ [MOD p] := by unfold Nat.ModEq; rw [h1, hℓ]
    rw [Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' (by have := hℓpri.out.two_le; omega)).mp hmod)]
  have hv0 : redHom hζ hμ (v : 𝓞 K) ≠ 0 := by
    rw [← coe_redUnit]; exact (redUnit hζ hμ v).ne_zero
  have key := redHom_eigen_pow_eq_Qi_pow (hζ := hζ) (hμ := hμ) (i := i) (hp := hp) (hℓ := hℓ)
    (hkeven := hkeven) (hieven := hieven) (hi2 := hi2) (hip := hip)
  rw [← key, hv, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, hpk,
    ZMod.pow_card_sub_one_eq_one hv0]

end Final

end QiSide

end FltVandiver
