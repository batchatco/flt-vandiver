import FltRegular.CaseII.InductionStep
import FltVandiver.Lemma92Step4
import CyclotomicNT.RegularPrimes
import CyclotomicNT.CaseII
open CyclotomicNT

/-!
# Washington §9.1 descent — the real infinite descent (Case II, Vandiver)

This file is the Case II descent of FLT for Vandiver primes. The Galois/unramified machinery
(Washington Lemma 9.1 + 9.2) is axiom-clean in `FltVandiver.Lemma92` /
`FltVandiver.Lemma92Step4`; this file is the §9.1 *descent itself*.

## ⚠️ Two caveats (important when reading this file)

1. **`kummersLemma_vandiver` is VACUOUS, and does NOT remove `refinedKummer`.** Its hypotheses
   (a unit `u` with `complexConj u = u⁻¹`, i.e. a *minus unit*, and `u ≡ 1 mod (1-ζ)ᵖ`) force
   `u = 1`: a minus unit is a root of unity (Mathlib `unitsMulComplexConjInv` lands in torsion),
   and the only root of unity `≡ 1 mod 𝔭ᵖ` is `1`. So it supplies no content, and the
   `refinedKummer` (`p`-adic-`L`) dependency was *not* actually eliminated. The substantive tool is
   the *element-level* `cyclotomic_p_dvd_classNumber` (a minus **element**, not a unit).

2. **Proving `𝔞(ζ)` itself principal (`B1_quotient_principal`/`B1_principal`) is not
   provable from `p ∤ h⁺` directly.** `[𝔞 ζ]` is a *minus-part* `p`-torsion
   class, which Vandiver does not
   kill. The conj-fixed engine only gives the *product* `𝔞(ζ)·𝔞(ζ⁻¹)` principal (= `J_principal`).

**Correct path (Washington's actual §9.1, "Route A"):** work with the minus **element**
`u = (-ζ⁻¹)(x+ζy)/(x+ζ⁻¹y)` (NOT a unit; it generates `(A₁/Ā₁)ᵖ`). Since `σ u = u⁻¹`, the Kummer
pairing makes `σ` act trivially on `Gal(K(u^{1/p})/K)`, so that extension is a *plus-part* quotient,
killed by `p ∤ h⁺` via `cyclotomic_p_dvd_classNumber`. Hence `u` is a `p`-th power, so `A₁/Ā₁` is
principal; with `A₁·Ā₁` principal (`J_principal`), `A₁` is principal, and the descent proceeds. This
needs an *element-level* Kummer-unramifiedness (flt-regular's `KummersLemma.isUnramified` is
unit-level — a generalization is required) but avoids BOTH Stickelberger and `p`-adic `L`.
The lemmas `bClass`/`b_pow_p_eq_one`/`b_mul_conj_b_eq_one`/`J_principal`/`a_pow_principal`/
`c_principal` below are the reusable class-group pieces for this route.

## Strategy (Washington §9.1, real version)

flt-regular's `FltRegular.CaseII.InductionStep` proves the **regular** descent step
`exists_solution` (smaller solution from a generalized equation `x^p + y^p = ε·(π^{m+1} z)^p` over
`K = ℚ(ζ_p)`). It uses regularity (`p ∤ h`) in exactly ONE place:
`InductionStep.a_div_principal`, via `isPrincipal_of_isPrincipal_pow_of_Coprime' _ hreg`, to make
    the
**non-real** class `𝔞 η / 𝔞₀` principal. The Kummer-unit step likewise uses the regular Kummer's
Lemma.

Washington's Vandiver descent replaces these two regularity uses by **Vandiver** (`p ∤ h⁺`) ones:
1. **Principality.** Restructure the descent around the **real** ideals `B_a` of `𝓞 K`
   (`(ω + ζ^a θ)/(1 - ζ^a) = B_aᵖ`, `B_{-a} = conj B_a`), with the working solution taken REAL
   (`ω, θ, ξ ∈ 𝓞 K⁺`, the generalized real equation). Then `B_0` is conjugation-fixed with `B_0ᵖ`
   principal, so `p ∤ h⁺` makes `B_0` principal — the PROVED `isPrincipal_of_conjFixed_of_pow`
   (`CyclotomicNT.CaseII`). This is genuinely different from flt-regular's `𝔞 η/𝔞₀` (which is not
   conjugation-fixed and needs full `p ∤ h`).
2. **Kummer unit.** The descent's real unit `η = η_a/η_b` is `≡ 1 mod (1-ζ)ᵖ` and minus-part
   (`conj η = η⁻¹`); `kummersLemma_vandiver` (this project) shows it is a `pᵗʰ` power —
       **axiom-free**,
   replacing flt-regular's regular Kummer's Lemma AND the project's `refinedKummer` axiom. So NO
   `BernoulliVandiver` is needed.

Combined with `p ∤ h⁺` upgrading `B_0` to principal, the unit-being-a-`pᵗʰ`-power yields a smaller
real solution, contradicting minimality — the infinite descent.

## Reusable from flt-regular `InductionStep` (regularity-free pieces, instantiate with REAL `x,y`)
`zeta_sub_one_dvd`, `span_pow_add_pow_eq`, the ideal cascade `𝔦/𝔠/𝔞`
(`root_div_zeta_sub_one_dvd_gcd_spec : (𝔞 η)ᵖ = 𝔠 η`), `coprime_c`, `p_dvd_c_iff`/`p_dvd_a_iff`,
`prod_c`, `formula`, `associated_eta_zero`. The cascade `def`s are accessible by full name
(`divZetaSubOneDvdGcd`, `rootDivZetaSubOneDvdGcd`); `η₀ := zetaSubOneDvdRoot` is the
unique root with `𝔭 ∣ 𝔠 η₀` (= the highly `π`-divisible factor `x+y`, so `η₀ = 1`). NOT reusable:
`a_div_principal`/`isPrincipal_a_div_a_zero` (regularity) → replace with the real route below.

## The (C6) recombination: Stage 1 / Stage 2

Docstrings below tag lemmas **(C6 Stage 1)** / **(C6 Stage 2)**; (C6) is the descent
recombination of `RouteA.lean`'s condition list, and the two stages are the descent's two
passes:

* **Stage 1** starts from the minimal REAL solution and recombines its two generator
  identities (`stage1_recombination`: `α₁ᵖ − σα₁ᵖ = unit·(x+y)/(ζ-1)`), producing an
  intermediate solution whose components form an **anti-conjugate pair**
  (`σ x = −y`, `σ y = −x`) — namely `(α₁, −σα₁)`.
* **Stage 2** reruns the ideal cascade on that anti-conjugate solution: its cascade ideal
  is conjugation-fixed (`sigma_i_antiConj`), so `p ∤ h⁺` gives principality *directly*,
  the generator is then upgraded to a REAL one (the `u^p = 1` chain ending in
  `real_generator`-style packaging), and the result is a strictly smaller real solution —
  closing the descent loop.

## Concrete lemma-by-lemma structure

NEW pieces (the genuinely-Vandiver work):
* `conj_i` : `σ(𝔦 η) = 𝔦 η⁻¹` (σ = `ringOfIntegersComplexConj`; from `x,y` real + `σ η = η⁻¹` for
    the
  root of unity η, `η⁻¹ = η^(p-1)` in `𝓞 K`). Then `conj_c : σ(𝔠 η) = 𝔠 η⁻¹` (from `𝔪·𝔠 η·𝔭 = 𝔦 η`,
  `𝔪`,`𝔭` conj-fixed), then `conj_a : σ(𝔞 η) = 𝔞 η⁻¹` (p-th-root uniqueness of ideals: `σ(𝔞 η)ᵖ =
  σ(𝔠 η) = 𝔠 η⁻¹ = (𝔞 η⁻¹)ᵖ`).
* COPRIMALITY CAVEAT: `isPrincipal_of_conjFixed_of_pow` REQUIRES coprime to
  `(p)`. `𝔞(1) = 𝔞(η₀)` is conj-fixed but NOT coprime (`η₀=1`). So feed the lemma the COPRIME
  conj-fixed PRODUCTS `J_a := 𝔞(ζᵃ)·𝔞(ζ⁻ᵃ)` (`a≠0`): conj-fixed (σ swaps factors), coprime to `(p)`
  (`p_dvd_a_iff`, `ζ^{±a}≠η₀`), `J_aᵖ` principal (`= 𝔠(ζᵃ)𝔠(ζ⁻ᵃ)`).
* `B1_quotient_principal` : `𝔞(ζ)/σ(𝔞(ζ))` principal — replaces
    `isPrincipal_of_isPrincipal_pow_of_Coprime'`.
  Via the `h⁺`-annihilator: `(𝔞 ζ)^{h⁺}` principal `= (β)`; `(α/ᾱ)^{h⁺} = (η/η̄)(β/β̄)ᵖ`; the
      minus-unit
  `u₁ := η/η̄ ≡ 1 mod 𝔭ᵖ` (since `α≡ᾱ mod p`, as `α≡x` real mod p), so `kummersLemma_vandiver` ⟹
  `u₁ = v₁ᵖ` ⟹ `α/ᾱ = unit·γᵖ` ⟹ quotient principal.
* `B1_principal` : `𝔞(ζ)` principal — from `J₁ = 𝔞(ζ)σ(𝔞(ζ))` principal (conjFixed lemma) AND
  `𝔞(ζ)/σ(𝔞(ζ))` principal, p odd ⟹ `𝔞(ζ)²`, hence `𝔞(ζ)`, principal.
* `descent_step` : the algebraic identity `(x+ζy)/(1-ζ) + (x+ζ⁻¹y)/(1-ζ⁻¹) = x+y`; substitute the
  principal generators `𝔞(ζ)=(α₁)`, `𝔞(1)=(α₀)`; the resulting unit `u₂ := ε₁/ε̄₁` is minus-part,
  `≡1 mod 𝔭ᵖ`, `kummersLemma_vandiver` ⟹ `u₂=v₂ᵖ`; get `(v₂α₁)ᵖ + ᾱ₁ᵖ = E·π^(…)·α₀ᵖ`; symmetrize
  `X' := v₂α₁+ᾱ₁`, `Y' := ζ(v₂α₁)+ζ⁻¹ᾱ₁` (both conj-fixed/REAL) ⟹ smaller real solution.
* `caseII_vandiver_descent` (below): minimality framing (cf. `not_exists_solution`) closes it.

## The formalization (below) -/

open scoped NumberField
open NumberField

namespace CaseIIVandiverDescent

open NumberField Ideal Polynomial NumberField.IsCMField NumberField.Units

variable {K : Type} {p : ℕ} [Fact p.Prime] [Field K] [NumberField K] [IsCMField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2)
  {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}
  {m : ℕ} (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
  (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
  (η : nthRootsFinset p (1 : 𝓞 K))

set_option quotPrecheck false
local notation "σ" => ringOfIntegersComplexConj K

/-- `hζ.unit'` packaged as a torsion unit, for `complexConj_torsion`. -/
noncomputable def ζ_torsion : torsion K :=
  ⟨hζ.unit', (CommGroup.mem_torsion hζ.unit').mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, NeZero.pos p, hζ.unit'_pow⟩)⟩

omit [IsCyclotomicExtension {p} ℚ K] in
lemma complexConj_unit : complexConj K (hζ.unit'.1 : K) = ((hζ.unit'⁻¹.1 : 𝓞 K) : K) :=
  IsCMField.complexConj_torsion K (ζ_torsion hζ)

omit [IsCyclotomicExtension {p} ℚ K] in
/-- `σ` (conjugation on `𝓞 K`) inverts the cyclotomic unit `ζ`. -/
lemma sigma_unit : (σ : 𝓞 K →+* 𝓞 K) hζ.unit'.1 = hζ.unit'⁻¹.1 := by
  have : (σ : 𝓞 K →+* 𝓞 K) hζ.unit'.1 = σ hζ.unit'.1 := rfl
  rw [this, RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj K, complexConj_unit hζ]

omit [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
lemma associated_unit_sub_one : Associated (hζ.unit'⁻¹.1 - 1) (hζ.unit'.1 - 1) := by
  use - hζ.unit'
  simp only [Units.val_neg, mul_neg, sub_mul, one_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one]
  ring

omit [IsCyclotomicExtension {p} ℚ K] in
/-- `σ 𝔭 = 𝔭`: conjugation fixes the prime above `p`. -/
lemma map_sigma_p :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.span {hζ.unit'.1 - 1}) = Ideal.span {hζ.unit'.1 - 1} := by
  rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, sigma_unit hζ,
    Ideal.span_singleton_eq_span_singleton]
  exact associated_unit_sub_one hζ

/-- `σ 𝔪 = 𝔪`: conjugation fixes the gcd ideal `gcd (x) (y)` for real `x, y`. -/
lemma map_sigma_m (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy : (σ : 𝓞 K →+* 𝓞 K) y = y) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (gcd (Ideal.span {x}) (Ideal.span {y}))
      = gcd (Ideal.span {x}) (Ideal.span {y}) := by
  rw [Ideal.gcd_eq_sup, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton, hx, hy]

omit [IsCMField K] in
include hp in
/-- Roots of unity of `K = ℚ(ζ_p)` (`p` odd) are `μ_{2p}`: `torsionOrder K = 2p`. -/
lemma torsionOrder_eq_two_mul : torsionOrder K = 2 * p := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).pos.ne'⟩
  have h := IsCyclotomicExtension.Rat.torsionOrder_eq (n := p) (K := K)
  rwa [if_neg (Nat.not_even_iff_odd.mpr ((Fact.out : Nat.Prime p).odd_of_ne_two hp))] at h

omit [IsCMField K] in
include hp in
/-- A `p`-th power of a torsion unit squares to `1` (since `|torsion ℚ(ζ_p)| = 2p`). -/
lemma torsion_pow_p_sq (s : torsion K) : (s ^ p) ^ 2 = 1 := by
  rw [← pow_mul]
  have hc : p * 2 = Fintype.card (torsion K) := by
    have := torsionOrder_eq_two_mul (K := K) hp
    simp only [NumberField.Units.torsionOrder] at this
    omega
  rw [hc, pow_card_eq_one]

include hp in
/-- **Order argument:** if `u^{p²} = 1` and `u^{2p} = 1` then `u^p = 1` (because
`gcd(p², 2p) = p` for `p` an odd prime). Used to collapse `u = σδ/δ` to a `p`-th root of unity. -/
lemma pow_p_eq_one_of_psq_2p {G : Type*} [Monoid G] {u : G}
    (h1 : u ^ (p ^ 2) = 1) (h2 : u ^ (2 * p) = 1) : u ^ p = 1 := by
  have hgcd : Nat.gcd (p ^ 2) (2 * p) = p := by
    have hcop : Nat.gcd p 2 = 1 :=
      (Nat.coprime_primes (Fact.out : Nat.Prime p) Nat.prime_two).mpr hp
    rw [sq, mul_comm 2 p, Nat.gcd_mul_left, hcop, mul_one]
  have hd : orderOf u ∣ p :=
    hgcd ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  exact orderOf_dvd_iff_pow_eq_one.mp hd

include hp in
omit [IsCMField K] in
/-- An element of `𝓞 K` that is a root of unity (`u^n = 1`, `n > 0`) satisfies `u^{2p} = 1`, since
    the
roots of unity of `ℚ(ζ_p)` form `μ_{2p}` (`|torsion| = 2p`). -/
lemma pow_2p_eq_one_of_pow_eq_one {u : 𝓞 K} {n : ℕ} (hn : 0 < n) (h : u ^ n = 1) :
    u ^ (2 * p) = 1 := by
  have hUu : IsUnit u :=
    IsUnit.of_mul_eq_one (u ^ (n - 1)) (by rw [← pow_succ', Nat.sub_add_cancel hn, h])
  obtain ⟨u', rfl⟩ := hUu
  have hu'n : u' ^ n = 1 := by
    apply Units.ext; rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h
  have htor : u' ∈ torsion K :=
    (CommGroup.mem_torsion _).mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hu'n⟩)
  have hc : Fintype.card (torsion K) = 2 * p := by
    have := torsionOrder_eq_two_mul (K := K) hp
    simp only [NumberField.Units.torsionOrder] at this; omega
  have hu'2p : u' ^ (2 * p) = 1 := by
    have hs : (⟨u', htor⟩ : torsion K) ^ (2 * p) = 1 := by rw [← hc]; exact pow_card_eq_one
    simpa using congrArg (fun s : torsion K => (s : (𝓞 K)ˣ)) hs
  rw [← Units.val_pow_eq_pow_val, hu'2p, Units.val_one]

include hζ hp in
/-- **`η_unit^p = ση_unit^p`.** From flt-regular's `unit_inv_conj_is_root_of_unity`
    (`η_unit/ση_unit`
is a square of a root of unity), raising to `p` kills it: `(η_unit/ση_unit)^p = 1`. -/
lemma eta_unit_pow_p (η_unit : (𝓞 K)ˣ) :
    (η_unit : 𝓞 K) ^ p = ((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K)) ^ p := by
  have hp2 : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hp)
  obtain ⟨m, hm⟩ := unit_inv_conj_is_root_of_unity hζ η_unit hp2
  have hpow1 : (η_unit * (unitsComplexConj K η_unit)⁻¹) ^ p = 1 := by
    rw [hm, ← pow_mul, ← pow_mul, show m * (2 * p) = p * (2 * m) from by ring, pow_mul]
    simp only [IsPrimitiveRoot.toInteger_isUnit_unit]
    rw [hζ.unit'_pow, one_pow]
  rw [mul_pow, inv_pow] at hpow1
  have huu : η_unit ^ p = (unitsComplexConj K η_unit) ^ p := mul_inv_eq_one.mp hpow1
  have hval := congrArg (Units.val) huu
  rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at hval

include hζ hp in
/-- A unit cannot satisfy `v = -σv`: the integer congruence `v ≡ b`, `σv ≡ b (mod 𝔭)` then forces
`𝔭 ∣ 2b`, so `p ∣ b` (p odd), whence `𝔭 ∣ v` — impossible for a unit. Rules out the `η = -1` branch
in `eps_real`. -/
lemma unit_ne_neg_conj (v : (𝓞 K)ˣ) :
    (↑v : 𝓞 K) ≠ - (σ : 𝓞 K →+* 𝓞 K) (↑v) := by
  intro hvσ
  obtain ⟨b, hb⟩ := exists_zeta_sub_one_dvd_sub_Int hζ (↑v : 𝓞 K)
  have hσπ : (σ : 𝓞 K →+* 𝓞 K) (hζ.unit'.1 - 1) = hζ.unit'⁻¹.1 - 1 := by
    rw [map_sub, map_one, sigma_unit hζ]
  have hbσ : (hζ.unit'.1 - 1) ∣ ((σ : 𝓞 K →+* 𝓞 K) (↑v) - (b : 𝓞 K)) := by
    have hd := map_dvd (σ : 𝓞 K →+* 𝓞 K) hb
    simp only [← IsPrimitiveRoot.coe_unit'] at hd
    rw [hσπ, map_sub, map_intCast] at hd
    exact (associated_unit_sub_one hζ).symm.dvd.trans hd
  have hσv : (σ : 𝓞 K →+* 𝓞 K) (↑v) = -↑v := by linear_combination hvσ
  rw [hσv] at hbσ
  have hsum := dvd_add hb hbσ
  have hrw : (↑v - (b : 𝓞 K)) + (-↑v - (b : 𝓞 K)) = -((2 * b : ℤ) : 𝓞 K) := by push_cast; ring
  rw [hrw] at hsum
  have h2b : (p : ℤ) ∣ 2 * b := (zeta_sub_one_dvd_Int_iff hζ).mp ((dvd_neg).mp hsum)
  have hpb : (p : ℤ) ∣ b := by
    rcases (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).dvd_mul.mp h2b with h2 | hb'
    · exfalso
      have hle := Int.le_of_dvd (by norm_num) h2
      have hp2 : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hp)
      omega
    · exact hb'
  have hπv : (hζ.unit'.1 - 1) ∣ (↑v : 𝓞 K) := by
    have hπb : (hζ.unit'.1 - 1) ∣ ((b : ℤ) : 𝓞 K) := (zeta_sub_one_dvd_Int_iff hζ).mpr hpb
    have := dvd_add hb hπb
    rwa [sub_add_cancel] at this
  have hπnu : ¬ IsUnit (hζ.unit'.1 - 1) := fun h =>
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').not_unit (Ideal.isUnit_iff.mpr
        (Ideal.span_singleton_eq_top.mpr h))
  exact hπnu (isUnit_of_dvd_unit hπv v.isUnit)

include hζ hp in
/-- **`ε` real (C6 — the `u = wᵖ` consequence).** If the torsion element `η = v·(σv)⁻¹` is a `p`-th
power of a torsion unit (which `u = wᵖ` forces via `u = (ε/σε)(α/σα)ᵖ`), then `v` is real
(`unitsComplexConj v = v`). Mechanism: `η² = s^{2p} = s^{card(torsion)} = 1` (roots of unity of
`ℚ(ζ_p)` are `μ_{2p}`), so `↑η = ±1`; `unit_ne_neg_conj` (the `𝔭`-congruence) rules out `−1`.
NO real-unit Kummer's Lemma, NO p-adic L. -/
lemma eps_real {v : (𝓞 K)ˣ} {s : torsion K}
    (hs : unitsMulComplexConjInv K v = s ^ p) :
    unitsComplexConj K v = v := by
  have hηu2 : (↑(unitsMulComplexConjInv K v) : (𝓞 K)ˣ) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hs, torsion_pow_p_sq hp s, OneMemClass.coe_one]
  have hval : (((↑(unitsMulComplexConjInv K v) : (𝓞 K)ˣ) : 𝓞 K)) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hηu2, Units.val_one]
  have hval2 : (((↑(unitsMulComplexConjInv K v) : (𝓞 K)ˣ) : 𝓞 K))
      * (((↑(unitsMulComplexConjInv K v) : (𝓞 K)ˣ) : 𝓞 K)) = 1 := by rw [← pow_two]; exact hval
  rcases mul_self_eq_one_iff.mp hval2 with h1 | h1
  · have hη1 : unitsMulComplexConjInv K v = 1 := by
      apply Subtype.ext; apply Units.ext; simpa using h1
    rw [unitsComplexConj_eq_self_iff, ← unitsMulComplexConjInv_ker, MonoidHom.mem_ker]
    exact hη1
  · exfalso
    have hunit : (↑(unitsMulComplexConjInv K v) : (𝓞 K)ˣ) = -1 := by
      apply Units.ext; simpa using h1
    rw [unitsMulComplexConjInv_apply, mul_inv_eq_iff_eq_mul] at hunit
    have hbridge : ((unitsComplexConj K v : (𝓞 K)ˣ) : 𝓞 K) = (σ : 𝓞 K →+* 𝓞 K) (↑v) := rfl
    apply unit_ne_neg_conj hp hζ v
    have hvc : (↑v : 𝓞 K) = -((unitsComplexConj K v : (𝓞 K)ˣ) : 𝓞 K) := by
      rw [show (↑v : 𝓞 K) = ((-1 * unitsComplexConj K v : (𝓞 K)ˣ) : 𝓞 K) from
        congrArg Units.val hunit]
      push_cast; ring
    exact hvc.trans (congrArg Neg.neg hbridge)

include hζ hp in
/-- `eps_real` in the form the recombination produces it: if the value of `v·(σv)⁻¹` is a `p`-th
power **in `K`** (which `u = wᵖ` gives, since `u = (ε/σε)(α/σα)ᵖ`), then `v` is real. The `K`-root
    is
automatically a torsion unit: `𝓞 K` is integrally closed (so the root lies in `𝓞 K`), and a unit
whose `p`-th power is a root of unity is itself a root of unity. -/
lemma eps_real' {v : (𝓞 K)ˣ} {t : K}
    (ht : (((unitsMulComplexConjInv K v : (𝓞 K)ˣ) : 𝓞 K) : K) = t ^ p) :
    unitsComplexConj K v = v := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  set c : 𝓞 K := ((unitsMulComplexConjInv K v : (𝓞 K)ˣ) : 𝓞 K) with hc
  have hint : IsIntegral (𝓞 K) t :=
    ⟨Polynomial.X ^ p - Polynomial.C c, Polynomial.monic_X_pow_sub_C c hp0, by simp [ht]⟩
  obtain ⟨t₀, ht₀⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have ht₀p : t₀ ^ p = c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [map_pow, ht₀]; exact ht.symm
  have hcu : IsUnit c := (unitsMulComplexConjInv K v : (𝓞 K)ˣ).isUnit
  obtain ⟨u₀, hu₀⟩ := isUnit_of_dvd_unit (ht₀p ▸ dvd_pow_self t₀ hp0) hcu
  have hu₀p : u₀ ^ p = (unitsMulComplexConjInv K v : (𝓞 K)ˣ) := by
    apply Units.ext; rw [Units.val_pow_eq_pow_val, hu₀, ht₀p]
  have hηfin : IsOfFinOrder (unitsMulComplexConjInv K v : (𝓞 K)ˣ) :=
    (CommGroup.mem_torsion _).mp (unitsMulComplexConjInv K v).2
  have hu₀tor : u₀ ∈ torsion K := by
    refine (CommGroup.mem_torsion u₀).mpr ?_
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨p * orderOf (unitsMulComplexConjInv K v : (𝓞 K)ˣ),
      Nat.mul_pos (Nat.pos_of_ne_zero hp0) hηfin.orderOf_pos,
      by rw [pow_mul, hu₀p, pow_orderOf_eq_one]⟩
  refine eps_real hp hζ (s := ⟨u₀, hu₀tor⟩) ?_
  apply Subtype.ext
  rw [Subgroup.coe_pow]
  exact hu₀p.symm

/-- **Coercion bridge.** In `K`, the value of the torsion element `v·(σv)⁻¹` is `ι(v)·ι(σv)⁻¹`
(`ι = algebraMap (𝓞 K) K`). Lets the recombination feed `eps_real'`. -/
lemma coe_umcci_field (v : (𝓞 K)ˣ) :
    (((unitsMulComplexConjInv K v : (𝓞 K)ˣ) : 𝓞 K) : K)
      = algebraMap (𝓞 K) K (v : 𝓞 K) * (algebraMap (𝓞 K) K ((σ : 𝓞 K →+* 𝓞 K) (v : 𝓞 K)))⁻¹ := by
  rw [RingOfIntegers.coe_eq_algebraMap, unitsMulComplexConjInv_apply, Units.val_mul, map_mul]
  congr 1
  have h1 : ((unitsComplexConj K v : (𝓞 K)ˣ) : 𝓞 K) = (σ : 𝓞 K →+* 𝓞 K) (v : 𝓞 K) := rfl
  rw [← h1]
  have key : algebraMap (𝓞 K) K ((unitsComplexConj K v : (𝓞 K)ˣ) : 𝓞 K)
      * algebraMap (𝓞 K) K (((unitsComplexConj K v)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact (inv_eq_of_mul_eq_one_right key).symm

omit [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
lemma η_inv_prop : (η : 𝓞 K) ^ (p - 1) ∈ nthRootsFinset p (1 : 𝓞 K) := by
  rw [Polynomial.mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul]
  have h_mem := η.2
  rw [Polynomial.mem_nthRootsFinset (NeZero.pos p)] at h_mem
  rw [h_mem, one_pow]

/-- The inverse root of unity `η⁻¹ = η^(p-1)` as a member of `nthRootsFinset`. -/
noncomputable def η_inv : nthRootsFinset p (1 : 𝓞 K) := ⟨(η : 𝓞 K) ^ (p - 1), η_inv_prop η⟩

omit [IsCMField K] in
lemma cancel_helper {I J D L : Ideal (𝓞 K)} (hI : I ≠ 0) (hD : D ≠ 0)
    (h : I * J * D = I * L * D) : J = L := by
  rw [mul_assoc, mul_assoc] at h
  exact mul_right_cancel₀ hD (mul_left_cancel₀ hI h)

/-- **`conj_c`** : `σ(𝔠 η) = 𝔠 (η⁻¹)`. -/
lemma conj_c (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y)
    (hci : Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.span {x + y * (η : 𝓞 K)})
      = Ideal.span {x + y * (η_inv η : 𝓞 K)}) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (divZetaSubOneDvdGcd hp hζ e hy η)
      = divZetaSubOneDvdGcd hp hζ e hy (η_inv η) := by
  have h_mul_inv := m_mul_c_mul_p hp hζ e hy (η_inv η)
  have h_map := congrArg (Ideal.map (σ : 𝓞 K →+* 𝓞 K)) (m_mul_c_mul_p hp hζ e hy η)
  simp only [← IsPrimitiveRoot.coe_unit'] at h_map
  rw [Ideal.map_mul, Ideal.map_mul, map_sigma_m hx hy_real, map_sigma_p hζ, hci] at h_map
  rw [← h_map] at h_mul_inv
  exact cancel_helper (m_ne_zero hζ hy) (p_ne_zero hζ) h_mul_inv.symm

/-- **`conj_a`** : `σ(𝔞 η) = 𝔞 (η⁻¹)`, by `p`-th-root uniqueness of ideals. -/
lemma conj_a (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y)
    (hci : Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.span {x + y * (η : 𝓞 K)})
      = Ideal.span {x + y * (η_inv η : 𝓞 K)}) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (rootDivZetaSubOneDvdGcd hp hζ e hy η)
      = rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η) := by
  have h_pow1 := root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy η
  have h_pow2 := root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy (η_inv η)
  dsimp only at h_pow1 h_pow2
  have h_map := congrArg (Ideal.map (σ : 𝓞 K →+* 𝓞 K)) h_pow1
  rw [Ideal.map_pow, conj_c hp hζ e hy η hx hy_real hci, ← h_pow2] at h_map
  exact pow_left_injective (Fact.out : Nat.Prime p).ne_zero h_map

/-- `σ 𝔪 = 𝔪` for an **anti-conjugate** pair (`σ x = -y`, `σ y = -x`): `σ` swaps `(x) ↔ (y)`. -/
lemma map_sigma_m_antiConj (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (gcd (Ideal.span {x}) (Ideal.span {y}))
      = gcd (Ideal.span {x}) (Ideal.span {y}) := by
  rw [Ideal.gcd_eq_sup, Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton,
    Set.image_singleton, hxa, hya, Ideal.span_singleton_neg, Ideal.span_singleton_neg, sup_comm]

/-- **`conj_c` (anti-conjugate)** : `σ(𝔠 η) = 𝔠 η` when `σ(𝔦 η) = 𝔦 η` (anti-conjugate `σx=-y,
    σy=-x`,
so the cascade factor is self-conjugate — `sigma_i_antiConj`). -/
lemma conj_c_antiConj (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    (hci : Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.span {x + y * (η : 𝓞 K)})
      = Ideal.span {x + y * (η : 𝓞 K)}) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (divZetaSubOneDvdGcd hp hζ e hy η)
      = divZetaSubOneDvdGcd hp hζ e hy η := by
  have h_mul := m_mul_c_mul_p hp hζ e hy η
  have h_map := congrArg (Ideal.map (σ : 𝓞 K →+* 𝓞 K)) (m_mul_c_mul_p hp hζ e hy η)
  simp only [← IsPrimitiveRoot.coe_unit'] at h_map
  rw [Ideal.map_mul, Ideal.map_mul, map_sigma_m_antiConj hxa hya, map_sigma_p hζ, hci] at h_map
  rw [← h_mul] at h_map
  exact cancel_helper (m_ne_zero hζ hy) (p_ne_zero hζ) h_map

/-- **`conj_a` (anti-conjugate)** : `σ(𝔞 η) = 𝔞 η`, by `p`-th-root uniqueness. The cascade ideal of
the anti-conjugate intermediate solution is conjugation-fixed (Stage-2 step 1). -/
lemma conj_a_antiConj (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    (hci : Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.span {x + y * (η : 𝓞 K)})
      = Ideal.span {x + y * (η : 𝓞 K)}) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (rootDivZetaSubOneDvdGcd hp hζ e hy η)
      = rootDivZetaSubOneDvdGcd hp hζ e hy η := by
  have h_pow1 := root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy η
  dsimp only at h_pow1
  have h_map := congrArg (Ideal.map (σ : 𝓞 K →+* 𝓞 K)) h_pow1
  rw [Ideal.map_pow, conj_c_antiConj hp hζ e hy η hxa hya hci, ← h_pow1] at h_map
  exact pow_left_injective (Fact.out : Nat.Prime p).ne_zero h_map

omit [IsCyclotomicExtension {p} ℚ K] in
include hp in
/-- **Stage-2 step 2 (real generator).** If `σ δ = u·δ` with `u` a `p`-th root of unity (the
conjugate-shift unit of the conj-fixed principal ideal `(δ)`), then `δ' = u^{(p+1)/2}·δ` is a
    **real**
generator of the same ideal. Key: `μ_p` has odd order, so `u = w²` with `w = u^{(p+1)/2}`, and
`σw·w = (σu·u)^{(p+1)/2} = 1`, giving `σ(wδ) = σw·u·δ = σw·w²·δ = (σw·w)·w·δ = w·δ`. -/
lemma exists_real_assoc {δ : 𝓞 K} (hδ : δ ≠ 0) {u : 𝓞 K} (hup : u ^ p = 1)
    (hσδ : (σ : 𝓞 K →+* 𝓞 K) δ = u * δ) :
    (σ : 𝓞 K →+* 𝓞 K) (u ^ ((p + 1) / 2) * δ) = u ^ ((p + 1) / 2) * δ := by
  have hinvol : (σ : 𝓞 K →+* 𝓞 K) ((σ : 𝓞 K →+* 𝓞 K) δ) = δ := by
    change ringOfIntegersComplexConj K (ringOfIntegersComplexConj K δ) = δ
    apply RingOfIntegers.coe_injective
    simp only [coe_ringOfIntegersComplexConj, complexConj_apply_apply]
  have hσuu : (σ : 𝓞 K →+* 𝓞 K) u * u = 1 := by
    have h := congrArg (σ : 𝓞 K →+* 𝓞 K) hσδ
    rw [hinvol, map_mul, hσδ, ← mul_assoc] at h
    exact mul_right_cancel₀ hδ (by rw [one_mul]; exact h.symm)
  set w := u ^ ((p + 1) / 2) with hw
  have hw2 : w * w = u := by
    rw [hw, ← pow_add,
      show (p + 1) / 2 + (p + 1) / 2 = p + 1 by
        obtain ⟨r, hr⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two hp; omega,
      pow_succ, hup, one_mul]
  have hσww : (σ : 𝓞 K →+* 𝓞 K) w * w = 1 := by rw [hw, map_pow, ← mul_pow, hσuu, one_pow]
  rw [map_mul, hσδ, ← hw2, ← mul_assoc, ← mul_assoc, hσww, one_mul]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- `σ η = η^(p-1)` for any root of unity `η ∈ nthRootsFinset` (generalizes `sigma_unit`). -/
lemma sigma_eta : (σ : 𝓞 K →+* 𝓞 K) (η : 𝓞 K) = (η : 𝓞 K) ^ (p - 1) := by
  have hηp : (η : 𝓞 K) ^ p = 1 := by
    have := η.2; rwa [Polynomial.mem_nthRootsFinset (NeZero.pos p)] at this
  have hmul : (η : 𝓞 K) ^ (p - 1) * (η : 𝓞 K) = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos p)]; exact hηp
  let u : (𝓞 K)ˣ := ⟨(η : 𝓞 K), (η : 𝓞 K) ^ (p - 1), by rw [mul_comm]; exact hmul, hmul⟩
  have hupow : u ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hηp)
  have hmem : u ∈ torsion K := (CommGroup.mem_torsion u).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, NeZero.pos p, hupow⟩)
  have hc : complexConj K ((η : 𝓞 K) : K) = ((η : 𝓞 K) : K)⁻¹ :=
    IsCMField.complexConj_torsion K ⟨u, hmem⟩
  have hb : (σ : 𝓞 K →+* 𝓞 K) (η : 𝓞 K) = σ (η : 𝓞 K) := rfl
  rw [hb, RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj K, hc]
  have hηpK : ((η : 𝓞 K) : K) ^ p = 1 := by exact_mod_cast hηp
  have hcoe : ((η : 𝓞 K) : K) ^ (p - 1) * ((η : 𝓞 K) : K) = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos p)]; exact hηpK
  push_cast
  exact inv_eq_of_mul_eq_one_left hcoe

omit [IsCyclotomicExtension {p} ℚ K] in
/-- The `conj_i` hypothesis, discharged: `σ(𝔦 η) = 𝔦 (η⁻¹)` for real `x, y`. -/
lemma conj_i (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.span {x + y * (η : 𝓞 K)})
      = Ideal.span {x + y * (η_inv η : 𝓞 K)} := by
  rw [Ideal.map_span, Set.image_singleton, map_add, map_mul, hx, hy_real, sigma_eta η]
  rfl

omit [IsCMField K] in
/-- `η_inv` is an involution on `nthRootsFinset`: `η_inv (η_inv η) = η`. -/
lemma η_inv_inv : η_inv (η_inv η) = η := by
  have hηp : (η : 𝓞 K) ^ p = 1 := by
    have := η.2; rwa [Polynomial.mem_nthRootsFinset (NeZero.pos p)] at this
  apply Subtype.ext
  change ((η : 𝓞 K) ^ (p - 1)) ^ (p - 1) = (η : 𝓞 K)
  obtain ⟨d, rfl⟩ : ∃ d, p = d + 2 := ⟨p - 2, by have := (Fact.out : Nat.Prime p).two_le; omega⟩
  rw [← pow_mul, show (d + 2 - 1) * (d + 2 - 1) = (d + 2) * (d + 2 - 2) + 1 by
    have e1 : d + 2 - 1 = d + 1 := by omega
    have e2 : d + 2 - 2 = d := by omega
    rw [e1, e2]; ring]
  rw [pow_add, pow_mul, hηp, one_pow, one_mul, pow_one]

/-- **`η₀` is conjugation-fixed** (`η₀⁻¹ = η₀`, hence `η₀ = 1`): `𝔭 ∣ 𝔞 η₀` and `σ` fixes `𝔭`, so
`𝔭 ∣ σ(𝔞 η₀) = 𝔞(η₀⁻¹)`; by uniqueness (`p_dvd_a_iff`) the only root with `𝔭 ∣ 𝔞 ·` is `η₀`. -/
lemma eta_zero_inv_eq (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y) :
    η_inv (zetaSubOneDvdRoot hp hζ e hy) = zetaSubOneDvdRoot hp hζ e hy := by
  have h1 : Ideal.span {hζ.unit'.1 - 1} ∣
      rootDivZetaSubOneDvdGcd hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy) :=
    (p_dvd_a_iff hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy)).mpr rfl
  obtain ⟨C, hC⟩ := h1
  have h2 : Ideal.span {hζ.unit'.1 - 1} ∣
      rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv (zetaSubOneDvdRoot hp hζ e hy)) := by
    rw [← conj_a hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy) hx hy_real
          (conj_i (zetaSubOneDvdRoot hp hζ e hy) hx hy_real), hC, Ideal.map_mul, map_sigma_p hζ]
    exact dvd_mul_right _ _
  exact (p_dvd_a_iff hp hζ e hy (η_inv (zetaSubOneDvdRoot hp hζ e hy))).mp h2

/-- **`η₀ = 1`.** From `eta_zero_inv_eq` (`a^(p-1) = a` for `a = ↑η₀`) and `a^p = 1`, get `a² = 1`;
`p` odd then forces `a = a^p = 1`. So the highly-`π`-divisible factor is `x + y`. -/
lemma eta_zero_eq_one (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y) :
    (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) = 1 := by
  set a : 𝓞 K := (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K) with ha
  have hap : a ^ p = 1 := by
    have h := (zetaSubOneDvdRoot hp hζ e hy).2
    rwa [Polynomial.mem_nthRootsFinset (NeZero.pos p)] at h
  have hinv : a ^ (p - 1) = a := Subtype.ext_iff.mp (eta_zero_inv_eq hp hζ e hy hx hy_real)
  have ha2 : a ^ 2 = 1 := by
    have e1 : a ^ p = a ^ 2 := by
      rw [← Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_lt.le, pow_succ, hinv]; ring
    rw [← e1]; exact hap
  obtain ⟨k, hk⟩ := (Fact.out : Nat.Prime p).odd_of_ne_two hp
  have hpa : a ^ p = a := by
    rw [hk, pow_add, pow_mul, ha2, one_pow, one_mul, pow_one]
  rw [← hpa]; exact hap

/-- **`𝔞₀` is conjugation-fixed**: `σ(𝔞 η₀) = 𝔞 η₀` (from `eta_zero_inv_eq`), then cancel `𝔭^m` in
`𝔭^m·𝔞₀ = 𝔞 η₀`. -/
lemma a_zero_conj_fixed (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (aEtaZeroDvdPPow hp hζ e hy)
      = aEtaZeroDvdPPow hp hζ e hy := by
  have hfix : Ideal.map (σ : 𝓞 K →+* 𝓞 K)
        (rootDivZetaSubOneDvdGcd hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy))
      = rootDivZetaSubOneDvdGcd hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy) := by
    rw [conj_a hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy) hx hy_real
          (conj_i (zetaSubOneDvdRoot hp hζ e hy) hx hy_real), eta_zero_inv_eq hp hζ e hy hx hy_real]
  have key := congrArg (Ideal.map (σ : 𝓞 K →+* 𝓞 K)) (a_eta_zero_dvd_p_pow_spec hp hζ e hy)
  simp only [← IsPrimitiveRoot.coe_unit'] at key
  rw [Ideal.map_mul, Ideal.map_pow, map_sigma_p hζ, hfix,
    ← a_eta_zero_dvd_p_pow_spec hp hζ e hy] at key
  exact mul_left_cancel₀ (pow_ne_zero m (p_ne_zero hζ)) key

omit [IsCMField K] in
/-- **`𝔞₀ᵖ` is principal**: `𝔭^{mp+1}·𝔞₀ᵖ = (x+yη₀)` (from `𝔞 η₀ᵖ = 𝔠 η₀`, `𝔠 η₀·𝔭 = (x+yη₀)`
under `𝔪=1`, and `𝔭^m·𝔞₀ = 𝔞 η₀`); since `𝔭 = (π)` and `(x+yη₀)` are principal, `𝔞₀ᵖ = (γ)` for
`γ = (x+yη₀)/π^{mp+1}`. -/
lemma a_zero_pow_principal (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    Submodule.IsPrincipal ((aEtaZeroDvdPPow hp hζ e hy) ^ p) := by
  have hpri : Fact (Nat.Prime p) := inferInstance
  have hπ0 : hζ.unit'.1 - 1 ≠ 0 := hζ.unit'_coe.sub_one_ne_zero hpri.out.one_lt
  have hceq : divZetaSubOneDvdGcd hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy)
      = (Ideal.span {hζ.unit'.1 - 1} ^ m) ^ p * (aEtaZeroDvdPPow hp hζ e hy) ^ p := by
    simp only [IsPrimitiveRoot.coe_unit']
    rw [← mul_pow, a_eta_zero_dvd_p_pow_spec hp hζ e hy,
        root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy)]
  have hc := m_mul_c_mul_p hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy)
  simp only [hm, one_mul] at hc
  rw [hceq, ← pow_mul, mul_right_comm] at hc
  simp only [← IsPrimitiveRoot.coe_unit'] at hc
  rw [← pow_succ, Ideal.span_singleton_pow] at hc
  have hdvd : (hζ.unit'.1 - 1) ^ (m * p + 1) ∣
      (x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 K)) := by
    rw [← Ideal.span_singleton_le_span_singleton, ← hc]
    exact Ideal.dvd_iff_le.mp (dvd_mul_right _ _)
  obtain ⟨γ, hγ⟩ := hdvd
  rw [hγ, ← Ideal.span_singleton_mul_span_singleton] at hc
  have hne : Ideal.span {(hζ.unit'.1 - 1) ^ (m * p + 1)} ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ hπ0
  rw [mul_left_cancel₀ hne hc]
  exact ⟨⟨γ, rfl⟩⟩

omit [IsCMField K] in
include hz in
/-- **`𝔞₀` is coprime to `(p)`**: `𝔭 ∤ 𝔞₀` (`not_p_div_a_zero`), and `(p) = 𝔭^{p-1}`. -/
lemma a_zero_coprime_p :
    IsCoprime (aEtaZeroDvdPPow hp hζ e hy) (Ideal.span {(p : 𝓞 K)}) := by
  have hpri : Fact (Nat.Prime p) := inferInstance
  have h_coprime : IsCoprime (aEtaZeroDvdPPow hp hζ e hy) (Ideal.span {hζ.unit'.1 - 1}) := by
    simp only [IsPrimitiveRoot.coe_unit']
    rw [Ideal.isCoprime_iff_gcd, gcd_comm, (Ideal.prime_span_singleton_iff.mpr
        hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff]
    exact not_p_div_a_zero hp hζ e hy hz
  have hp_pos : 0 < p - 1 := by have := hpri.out.two_le; omega
  have h_pow : IsCoprime (aEtaZeroDvdPPow hp hζ e hy)
      ((Ideal.span {hζ.unit'.1 - 1}) ^ (p - 1)) := by rwa [IsCoprime.pow_right_iff hp_pos]
  have h_assoc : Associated ((hζ.unit' - 1 : 𝓞 K) ^ (p - 1)) (p : 𝓞 K) :=
    associated_zeta_sub_one_pow_prime hζ
  have h_span : Ideal.span {(p : 𝓞 K)} = Ideal.span {((hζ.unit' - 1 : 𝓞 K) ^ (p - 1))} := by
    rw [Ideal.span_singleton_eq_span_singleton]; exact h_assoc.symm
  have h_eq : (hζ.unit' - 1 : 𝓞 K) = hζ.unit'.1 - 1 := rfl
  rw [h_eq] at h_span
  rw [h_span, ← Ideal.span_singleton_pow]
  exact h_pow

/-- **`J_a` is conjugation-fixed**: `σ(𝔞 η · 𝔞 η⁻¹) = 𝔞 η · 𝔞 η⁻¹`. The product `J_a := B_a·B_{-a}`
is the real (conj-fixed) ideal fed to `isPrincipal_of_conjFixed_of_pow`. -/
lemma J_conj_fixed (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K)
        (rootDivZetaSubOneDvdGcd hp hζ e hy η
          * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η))
      = rootDivZetaSubOneDvdGcd hp hζ e hy η
          * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η) := by
  rw [Ideal.map_mul, conj_a hp hζ e hy η hx hy_real (conj_i η hx hy_real),
    conj_a hp hζ e hy (η_inv η) hx hy_real (conj_i (η_inv η) hx hy_real),
    η_inv_inv η, mul_comm]

lemma J_coprime_p (_hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (_hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y)
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη' : η_inv η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    IsCoprime (rootDivZetaSubOneDvdGcd hp hζ e hy η
             * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η))
             (Ideal.span {(p : 𝓞 K)}) := by
  have hpri : Fact (Nat.Prime p) := inferInstance
  have h_coprime : IsCoprime (rootDivZetaSubOneDvdGcd hp hζ e hy η)
      (Ideal.span {hζ.unit'.1 - 1}) := by
    simp only [IsPrimitiveRoot.coe_unit']
    rw [Ideal.isCoprime_iff_gcd, gcd_comm, (Ideal.prime_span_singleton_iff.mpr
        hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff]
    rw [p_dvd_a_iff hp hζ e hy η]
    exact hη
  have h_coprime' : IsCoprime (rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η))
      (Ideal.span {hζ.unit'.1 - 1}) := by
    simp only [IsPrimitiveRoot.coe_unit']
    rw [Ideal.isCoprime_iff_gcd, gcd_comm, (Ideal.prime_span_singleton_iff.mpr
        hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff]
    rw [p_dvd_a_iff hp hζ e hy (η_inv η)]
    exact hη'
  have h_prod_coprime : IsCoprime (rootDivZetaSubOneDvdGcd hp hζ e hy η
    * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η)) (Ideal.span {hζ.unit'.1 - 1}) :=
    IsCoprime.mul_left h_coprime h_coprime'
  have hp_pos : 0 < p - 1 := by
    have := hpri.out.two_le
    omega
  have h_pow_coprime : IsCoprime (rootDivZetaSubOneDvdGcd hp hζ e hy η
      * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η))
      ((Ideal.span {hζ.unit'.1 - 1}) ^ (p - 1)) := by
    rwa [IsCoprime.pow_right_iff hp_pos]
  have h_assoc : Associated ((hζ.unit' - 1 : 𝓞 K) ^ (p - 1)) (p : 𝓞 K) :=
    associated_zeta_sub_one_pow_prime hζ
  have h_span : Ideal.span {(p : 𝓞 K)} = Ideal.span {((hζ.unit' - 1 : 𝓞 K) ^ (p - 1))} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    exact h_assoc.symm
  have h_eq : (hζ.unit' - 1 : 𝓞 K) = hζ.unit'.1 - 1 := rfl
  rw [h_eq] at h_span
  rw [h_span, ← Ideal.span_singleton_pow]
  exact h_pow_coprime

lemma J_pow_principal (_hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (_hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    Submodule.IsPrincipal ((rootDivZetaSubOneDvdGcd hp hζ e hy η
      * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η)) ^ p) := by
  have hpri : Fact (Nat.Prime p) := inferInstance
  have h_pow : ((rootDivZetaSubOneDvdGcd hp hζ e hy η
        * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η)) ^ p) =
      (divZetaSubOneDvdGcd hp hζ e hy η * divZetaSubOneDvdGcd hp hζ e hy (η_inv η)) := by
    rw [mul_pow, root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy η,
      root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy (η_inv η)]
  rw [h_pow]
  have h1 := m_mul_c_mul_p hp hζ e hy η
  have h2 := m_mul_c_mul_p hp hζ e hy (η_inv η)
  rw [hm, one_mul] at h1 h2
  simp only [← IsPrimitiveRoot.coe_unit'] at h1 h2
  have h_prod_raw : (divZetaSubOneDvdGcd hp hζ e hy η * Ideal.span {hζ.unit'.1 - 1})
      * (divZetaSubOneDvdGcd hp hζ e hy (η_inv η) * Ideal.span {hζ.unit'.1 - 1}) =
      Ideal.span {x + y * (η : 𝓞 K)} * Ideal.span {x + y * (η_inv η : 𝓞 K)} := by
    rw [h1, h2]
  have h_rearrange : (divZetaSubOneDvdGcd hp hζ e hy η * Ideal.span {hζ.unit'.1 - 1})
      * (divZetaSubOneDvdGcd hp hζ e hy (η_inv η) * Ideal.span {hζ.unit'.1 - 1}) =
      (divZetaSubOneDvdGcd hp hζ e hy η * divZetaSubOneDvdGcd hp hζ e hy (η_inv η))
        * (Ideal.span {hζ.unit'.1 - 1} * Ideal.span {hζ.unit'.1 - 1}) := by
    rw [mul_assoc, mul_comm (Ideal.span {hζ.unit'.1 - 1}), mul_assoc, mul_assoc]
  rw [h_rearrange] at h_prod_raw
  rw [Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_mul_span_singleton] at h_prod_raw
  have h_ne : Ideal.span {(hζ.unit'.1 - 1) * (hζ.unit'.1 - 1)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, mul_eq_zero]
    intro h_zero
    have hp_one_lt : 1 < p := by
      have hp_prime : Nat.Prime p := Fact.out
      exact hp_prime.one_lt
    have h_sub_one := hζ.unit'_coe.sub_one_ne_zero hp_one_lt
    cases h_zero with
    | inl h_l => exact h_sub_one h_l
    | inr h_r => exact h_sub_one h_r
  have h_le : Ideal.span {(x + y * (η : 𝓞 K)) * (x + y * (η_inv η : 𝓞 K))}
      ≤ Ideal.span {(hζ.unit'.1 - 1) * (hζ.unit'.1 - 1)} := by
    rw [← h_prod_raw]
    exact Ideal.mul_le_left
  rw [Ideal.span_singleton_le_span_singleton (α := 𝓞 K)] at h_le
  rcases h_le with ⟨γ, h_γ⟩
  have h_eq_prod : Ideal.span {(x + y * (η : 𝓞 K)) * (x + y * (η_inv η : 𝓞 K))} =
      Ideal.span {γ} * Ideal.span {(hζ.unit'.1 - 1) * (hζ.unit'.1 - 1)} := by
    rw [h_γ, mul_comm ((hζ.unit'.1 - 1) * (hζ.unit'.1 - 1)) γ,
      ← Ideal.span_singleton_mul_span_singleton]
  rw [h_eq_prod] at h_prod_raw
  have h_cancel := mul_right_cancel₀ h_ne h_prod_raw
  exact ⟨⟨γ, h_cancel⟩⟩

omit [IsCMField K] in
/-- With `𝔪 = (1)`, the ideal `𝔠 η` is principal. From `𝔠 η · 𝔭 = 𝔦 η = span {x + y·η}` (the
`𝔪 = 1` case of `m_mul_c_mul_p`), with both `𝔭 = span {ζ-1}` and `𝔦 η` principal singletons,
cancelling the principal `𝔭` exhibits a generator. -/
lemma c_principal (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    (divZetaSubOneDvdGcd hp hζ e hy η).IsPrincipal := by
  have h1 := m_mul_c_mul_p hp hζ e hy η
  rw [hm, one_mul] at h1
  have h_ne : (Ideal.span {hζ.unit'.1 - 1} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.unit'_coe.sub_one_ne_zero (Fact.out : Nat.Prime p).one_lt
  have h_le : Ideal.span {x + y * (η : 𝓞 K)} ≤ Ideal.span {hζ.unit'.1 - 1} := by
    rw [← h1]; exact Ideal.mul_le_left
  rw [Ideal.span_singleton_le_span_singleton (α := 𝓞 K)] at h_le
  rcases h_le with ⟨γ, h_γ⟩
  have h_eq : Ideal.span {x + y * (η : 𝓞 K)}
      = Ideal.span {γ} * Ideal.span {hζ.unit'.1 - 1} := by
    rw [h_γ, mul_comm (hζ.unit'.1 - 1) γ, ← Ideal.span_singleton_mul_span_singleton]
  rw [h_eq] at h1
  exact ⟨⟨γ, mul_right_cancel₀ h_ne h1⟩⟩

omit [IsCMField K] in
/-- With `𝔪 = (1)`, `𝔞(η)ᵖ` is principal (it equals `𝔠 η`, which is principal by `c_principal`).
This is one of the two coprime-exponent inputs (`p` and `2`) for proving `𝔞(η)` itself principal. -/
lemma a_pow_principal (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    ((rootDivZetaSubOneDvdGcd hp hζ e hy η) ^ p).IsPrincipal := by
  rw [root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy η]
  exact c_principal hp hζ e hy η hm

omit [IsCMField K] in
/-- **`𝔞(η)` is coprime to `(p)`** for `η ≠ η₀` (then `𝔭 ∤ 𝔞(η)` by `p_dvd_a_iff`, and
`(p) = 𝔭^{p-1}`). General-`η` companion of `a_zero_coprime_p`. -/
lemma a_coprime_p (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    IsCoprime (rootDivZetaSubOneDvdGcd hp hζ e hy η) (Ideal.span {(p : 𝓞 K)}) := by
  have hpri : Fact (Nat.Prime p) := inferInstance
  have h_coprime : IsCoprime (rootDivZetaSubOneDvdGcd hp hζ e hy η)
      (Ideal.span {hζ.unit'.1 - 1}) := by
    simp only [IsPrimitiveRoot.coe_unit']
    rw [Ideal.isCoprime_iff_gcd, gcd_comm, (Ideal.prime_span_singleton_iff.mpr
        hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff,
      p_dvd_a_iff hp hζ e hy η]
    exact hη
  have hp_pos : 0 < p - 1 := by have := hpri.out.two_le; omega
  have h_pow : IsCoprime (rootDivZetaSubOneDvdGcd hp hζ e hy η)
      ((Ideal.span {hζ.unit'.1 - 1}) ^ (p - 1)) := by rwa [IsCoprime.pow_right_iff hp_pos]
  have h_assoc : Associated ((hζ.unit' - 1 : 𝓞 K) ^ (p - 1)) (p : 𝓞 K) :=
    associated_zeta_sub_one_pow_prime hζ
  have h_span : Ideal.span {(p : 𝓞 K)} = Ideal.span {((hζ.unit' - 1 : 𝓞 K) ^ (p - 1))} := by
    rw [Ideal.span_singleton_eq_span_singleton]; exact h_assoc.symm
  have h_eq : (hζ.unit' - 1 : 𝓞 K) = hζ.unit'.1 - 1 := rfl
  rw [h_eq] at h_span
  rw [h_span, ← Ideal.span_singleton_pow]
  exact h_pow

omit [IsCMField K] in
/-- Under `𝔪 = (1)`: the ideal `(x + y·η)` factors as `𝔞(η)ᵖ · 𝔭`. The integral-ideal precursor to
Route A's (C2) identity `(u) = (𝔞(ζ)/𝔞(ζ⁻¹))ᵖ` (`FltVandiver.RouteA`): the `𝔭` factors of the
numerator `(x+ζy)` and denominator `(x+ζ⁻¹y)` of `u` cancel, leaving the `p`-th power. -/
lemma span_eq_a_pow_mul_p (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    Ideal.span {x + y * (η : 𝓞 K)}
      = (rootDivZetaSubOneDvdGcd hp hζ e hy η) ^ p * Ideal.span {hζ.unit'.1 - 1} := by
  have h1 := m_mul_c_mul_p hp hζ e hy η
  rw [hm, one_mul] at h1
  simp only [← IsPrimitiveRoot.coe_unit'] at h1
  rw [root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy η, h1]

/-- **(C6 Stage 1 → Stage 2 bridge), element level.** From the two generator identities
`x + y·ζ = ε(ζ-1)α` and `x + y·ζ⁻¹ = ε(ζ⁻¹-1)β` (the second using `ε₁` **real**, so the *same* unit
`ε` appears), the recombination collapses to `(1+ζ)(x+y) = ε(ζ-1)(α-β)`. Instantiated with
`α = α₁ᵖ`, `β = (σα₁)ᵖ`, this is Washington's `α₁ᵖ − σα₁ᵖ = unit·(x+y)/(ζ-1)`. -/
lemma stage1_recombination {R : Type*} [CommRing R] (x y ε ζ ζinv α β : R) (hinv : ζ * ζinv = 1)
    (hgen1 : x + y * ζ = ε * (ζ - 1) * α) (hgen2 : x + y * ζinv = ε * (ζinv - 1) * β) :
    (1 + ζ) * (x + y) = ε * (ζ - 1) * (α - β) := by
  linear_combination hgen1 + ζ * hgen2 + (ε * β - y) * hinv

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **(C6 Stage 2) the intermediate solution's cascade ideal is conjugation-fixed.** For an
**anti-conjugate** pair (`σ x = -y`, `σ y = -x` — exactly the `(α₁, -σα₁)` produced by Stage 1's
recombination), `σ(x + y·η) = -η⁻¹·(x + y·η)`, so the ideal `(x + y·η)` is `σ`-invariant. Hence its
class is in the plus-part and `p∤h⁺` makes `𝔞(η)` principal *directly* — no minus-element, no
unramifiedness axiom. (Contrast `conj_i`, the real case, where `σ(𝔦 η) = 𝔦(η⁻¹)`.) -/
lemma sigma_i_antiConj (hx : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hy : (σ : 𝓞 K →+* 𝓞 K) y = -x) :
    Ideal.map (σ : 𝓞 K →+* 𝓞 K) (Ideal.span {x + y * (η : 𝓞 K)})
      = Ideal.span {x + y * (η : 𝓞 K)} := by
  have hηp : (η : 𝓞 K) ^ p = 1 := by
    have := η.2; rwa [Polynomial.mem_nthRootsFinset (NeZero.pos p)] at this
  have hpe : (η : 𝓞 K) ^ (p - 1) * (η : 𝓞 K) = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_lt.le, hηp]
  have hηunit : IsUnit (η : 𝓞 K) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hpe)
  rw [Ideal.map_span, Set.image_singleton, map_add, map_mul, hx, hy, sigma_eta η,
      Ideal.span_singleton_eq_span_singleton]
  refine ⟨-hηunit.unit, ?_⟩
  rw [Units.val_neg, hηunit.unit_spec]
  linear_combination x * hpe

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Element-level conjugation factor** for an anti-conjugate pair: `σ(x+y·η) = -η^{p-1}·(x+y·η)`.
The element form of `sigma_i_antiConj`, used to conjugate the generator identity. -/
lemma sigma_factor_antiConj (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x) :
    (σ : 𝓞 K →+* 𝓞 K) (x + y * (η : 𝓞 K)) = -(η : 𝓞 K) ^ (p - 1) * (x + y * (η : 𝓞 K)) := by
  have hηp : (η : 𝓞 K) ^ p = 1 := by
    have := η.2; rwa [Polynomial.mem_nthRootsFinset (NeZero.pos p)] at this
  have hpe : (η : 𝓞 K) ^ (p - 1) * (η : 𝓞 K) = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_lt.le, hηp]
  rw [map_add, map_mul, hxa, hya, sigma_eta η]
  linear_combination y * hpe

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **(C6 Stage 2) conjugation of the generator identity.** Conjugating `x+y·η = η_unit·(ζ₀-1)·δᵖ`
(anti-conjugate solution) via `sigma_factor_antiConj` and cancelling the shared `(ζ₀-1)`:
`η^{p-1}·η_unit·δᵖ = σ(η_unit)·ζ₀⁻¹·(σδ)ᵖ`. Rearranged, `(σδ/δ)ᵖ = (η_unit/ση_unit)·(root of
    unity)`;
since `η_unit/ση_unit ∈ μ_p` (flt-regular `unit_inv_conj_is_root_of_unity`), this forces
`(σδ/δ)ᵖ ∈ μ_p`, hence `σδ/δ ∈ μ_p`, hence `δ` is real-adjustable (`exists_real_assoc`). -/
lemma gen_conj_eqn (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    {δ : 𝓞 K} {η_unit : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ ^ p) :
    (η : 𝓞 K) ^ (p - 1) * (η_unit : 𝓞 K) * δ ^ p
      = (σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * hζ.unit'⁻¹.1 * ((σ : 𝓞 K →+* 𝓞 K) δ) ^ p := by
  have hπ : hζ.unit'.1 - 1 ≠ 0 := hζ.unit'_coe.sub_one_ne_zero (Fact.out : Nat.Prime p).one_lt
  have hinv : hζ.unit'⁻¹.1 * hζ.unit'.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 := sigma_factor_antiConj η hxa hya
  have h2 : (σ : 𝓞 K →+* 𝓞 K) (x + y * (η : 𝓞 K))
      = (σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * (hζ.unit'⁻¹.1 - 1) * ((σ : 𝓞 K →+* 𝓞 K) δ) ^ p := by
    rw [hgen, map_mul, map_mul, map_pow, map_sub, map_one, sigma_unit hζ]
  have hcomb := h1.symm.trans h2
  rw [hgen] at hcomb
  apply mul_left_cancel₀ hπ
  linear_combination -hcomb - ((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * ((σ : 𝓞 K →+* 𝓞 K) δ) ^ p) * hinv

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **(C6 Stage 2) extract `u^p`.** With `σδ = u·δ` (the conjugate-shift unit of the conj-fixed
    ideal),
`gen_conj_eqn` + cancelling `δᵖ` gives `η^{p-1}·η_unit·ζ₀ = σ(η_unit)·uᵖ` — i.e. `uᵖ` equals the
    unit
`c = η^{p-1}·η_unit·ζ₀/σ(η_unit)`. Since `η_unit/ση_unit ∈ μ_p` and `η^{p-1}ζ₀ ∈ μ_p`, `c ∈ μ_p`
(`cᵖ=1`); with `u` a root of unity this forces `uᵖ=1` → `exists_real_assoc` → `δ` real. -/
lemma u_pow_eq (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    {δ : 𝓞 K} {η_unit : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ ^ p) (hδ : δ ≠ 0)
    {u : 𝓞 K} (hu : (σ : 𝓞 K →+* 𝓞 K) δ = u * δ) :
    (η : 𝓞 K) ^ (p - 1) * (η_unit : 𝓞 K) * hζ.unit'.1
      = (σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * u ^ p := by
  have hinv : hζ.unit'⁻¹.1 * hζ.unit'.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h := gen_conj_eqn hζ η hxa hya hgen
  rw [hu, mul_pow] at h
  have h2 : (η : 𝓞 K) ^ (p - 1) * (η_unit : 𝓞 K)
      = (σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * hζ.unit'⁻¹.1 * u ^ p :=
    mul_right_cancel₀ (pow_ne_zero p hδ) (by linear_combination h)
  linear_combination hζ.unit'.1 * h2 + ((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * u ^ p) * hinv

include hp in
/-- **(C6 Stage 2) `u^{p²} = 1`.** Raising `u_pow_eq` to the `p` and using `η^p=1`, `ζ₀^p=1`, and
`eta_unit_pow_p` (`η_unit^p = ση_unit^p`) collapses everything to `ση_unit^p·u^{p²} = ση_unit^p`. -/
lemma u_pow_psq_eq_one (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    {δ : 𝓞 K} {η_unit : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ ^ p) (hδ : δ ≠ 0)
    {u : 𝓞 K} (hu : (σ : 𝓞 K →+* 𝓞 K) δ = u * δ) :
    u ^ (p ^ 2) = 1 := by
  have hζ0p : (hζ.unit'.1 : 𝓞 K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.unit'_pow, Units.val_one]
  have hηp : (η : 𝓞 K) ^ p = 1 := by
    have := η.2; rwa [Polynomial.mem_nthRootsFinset (NeZero.pos p)] at this
  have hsne : ((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K)) ^ p ≠ 0 :=
    pow_ne_zero p ((map_ne_zero_iff _ (ringOfIntegersComplexConj K).injective).mpr (Units.ne_zero
        η_unit))
  have hue := u_pow_eq hζ η hxa hya hgen hδ hu
  have h : ((η : 𝓞 K) ^ (p - 1) * (η_unit : 𝓞 K) * hζ.unit'.1) ^ p
      = ((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * u ^ p) ^ p := by rw [hue]
  have hL : ((η : 𝓞 K) ^ (p - 1) * (η_unit : 𝓞 K) * hζ.unit'.1) ^ p = ((η_unit : 𝓞 K)) ^ p := by
    rw [mul_pow, mul_pow, ← pow_mul, hζ0p, mul_one, mul_comm (p - 1) p, pow_mul, hηp, one_pow,
        one_mul]
  have hR : ((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * u ^ p) ^ p
      = ((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K)) ^ p * u ^ (p ^ 2) := by
    rw [mul_pow, ← pow_mul, sq]
  rw [hL, hR, eta_unit_pow_p hp hζ η_unit] at h
  exact mul_left_cancel₀ hsne (h.symm.trans (mul_one _).symm)

include hp in
/-- **(C6 Stage 2) `u^p = 1`** — the conjugate-shift unit of the conj-fixed generator is a `p`-th
    root
of unity. Combines `u^{p²}=1` (`u_pow_psq_eq_one`) and `u^{2p}=1` (`pow_2p_eq_one_of_pow_eq_one`)
    via
`gcd(p²,2p)=p`. So `exists_real_assoc` yields a **real** generator. -/
lemma u_pow_p_eq_one (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    {δ : 𝓞 K} {η_unit : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ ^ p) (hδ : δ ≠ 0)
    {u : 𝓞 K} (hu : (σ : 𝓞 K →+* 𝓞 K) δ = u * δ) :
    u ^ p = 1 := by
  have hsq := u_pow_psq_eq_one hp hζ η hxa hya hgen hδ hu
  have h2p := pow_2p_eq_one_of_pow_eq_one hp (pow_pos (Fact.out : Nat.Prime p).pos 2) hsq
  exact pow_p_eq_one_of_psq_2p hp hsq h2p

include hp in
/-- **(C6 Stage 2) real generator.** The conj-fixed cascade ideal `(δ)` of the anti-conjugate
intermediate solution has a **real** generator `δ' = u^{(p+1)/2}·δ` (`u = σδ/δ`), and since `u^p=1`
we have `δ'ᵖ = δᵖ`, so the generator identity transfers: `x+y·η = η_unit·(ζ₀-1)·δ'ᵖ` with `σδ' =
    δ'`.
This is the crux of the anti-conjugate descent. -/
lemma exists_real_gen (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    {δ : 𝓞 K} {η_unit : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ ^ p) (hδ : δ ≠ 0)
    {u : 𝓞 K} (hu : (σ : 𝓞 K →+* 𝓞 K) δ = u * δ) :
    ∃ δ' : 𝓞 K, (σ : 𝓞 K →+* 𝓞 K) δ' = δ'
      ∧ x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ' ^ p := by
  have hup := u_pow_p_eq_one hp hζ η hxa hya hgen hδ hu
  refine ⟨u ^ ((p + 1) / 2) * δ, exists_real_assoc hp hδ hup hu, ?_⟩
  rw [hgen, mul_pow, ← pow_mul, show (p + 1) / 2 * p = p * ((p + 1) / 2) from mul_comm _ _,
    pow_mul, hup, one_pow, one_mul]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **(C6 Stage 2) `σδ = u·δ`.** `gen_conj_eqn` reads `(unit)·δᵖ = (unit)·(σδ)ᵖ`, so `δᵖ ~ (σδ)ᵖ`;
hence `span{δ}ᵖ = span{σδ}ᵖ`, and `p`-th-root uniqueness of ideals gives `span{δ} = span{σδ}`, i.e.
`Associated δ (σδ)`. This is the input `exists_real_gen` consumes. -/
lemma sigma_gen_assoc (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    {δ : 𝓞 K} {η_unit : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ ^ p) :
    ∃ u : 𝓞 K, (σ : 𝓞 K →+* 𝓞 K) δ = u * δ := by
  have hηp : (η : 𝓞 K) ^ p = 1 := by
    have := η.2; rwa [Polynomial.mem_nthRootsFinset (NeZero.pos p)] at this
  have hηU : IsUnit ((η : 𝓞 K) ^ (p - 1)) :=
    (IsUnit.of_mul_eq_one ((η : 𝓞 K) ^ (p - 1))
      (by rw [← pow_succ', Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le]; exact hηp)).pow _
  have hAU : IsUnit ((η : 𝓞 K) ^ (p - 1) * (η_unit : 𝓞 K)) := hηU.mul η_unit.isUnit
  have hBU : IsUnit ((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * hζ.unit'⁻¹.1) :=
    (η_unit.isUnit.map (σ : 𝓞 K →+* 𝓞 K)).mul (hζ.unit'⁻¹).isUnit
  have h := gen_conj_eqn hζ η hxa hya hgen
  have hspan : Ideal.span {δ ^ p} = Ideal.span {((σ : 𝓞 K →+* 𝓞 K) δ) ^ p} := by
    have hL : Ideal.span {((η : 𝓞 K) ^ (p - 1) * (η_unit : 𝓞 K)) * δ ^ p} = Ideal.span {δ ^ p} :=
      Ideal.span_singleton_eq_span_singleton.mpr (by
        simpa using (associated_one_iff_isUnit.mpr hAU).mul_right (δ ^ p))
    have hR : Ideal.span {((σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) * hζ.unit'⁻¹.1)
        * ((σ : 𝓞 K →+* 𝓞 K) δ) ^ p} = Ideal.span {((σ : 𝓞 K →+* 𝓞 K) δ) ^ p} :=
      Ideal.span_singleton_eq_span_singleton.mpr (by
        simpa using (associated_one_iff_isUnit.mpr hBU).mul_right (((σ : 𝓞 K →+* 𝓞 K) δ) ^ p))
    rw [← hL, ← hR, h]
  rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow] at hspan
  have hsp : Ideal.span {δ} = Ideal.span {(σ : 𝓞 K →+* 𝓞 K) δ} :=
    pow_left_injective (Fact.out : Nat.Prime p).ne_zero hspan
  rw [Ideal.span_singleton_eq_span_singleton] at hsp
  obtain ⟨v, hv⟩ := hsp
  exact ⟨v, by rw [← hv]; ring⟩

include hp in
/-- **(C6 Stage 2) real generator, packaged.** From the anti-conjugate generator identity alone
(`σδ=u·δ` extracted via `sigma_gen_assoc`, `u^p=1` via `u_pow_p_eq_one`), the cascade ideal `𝔞(η)`
of the anti-conjugate solution has a **real** generator `δ'` with `x+y·η = η_unit·(ζ₀-1)·δ'ᵖ`. -/
lemma exists_real_gen_of_gen (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    {δ : 𝓞 K} {η_unit : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ ^ p) (hδ : δ ≠ 0) :
    ∃ δ' : 𝓞 K, (σ : 𝓞 K →+* 𝓞 K) δ' = δ'
      ∧ x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ' ^ p := by
  obtain ⟨u, hu⟩ := sigma_gen_assoc hζ η hxa hya hgen
  exact exists_real_gen hp hζ η hxa hya hgen hδ hu

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **(C6 Stage 2) conjugate of the unit `η_unit`** when the generator is **real** (`σδ=δ`):
`ση_unit = η^{p-1}·η_unit·ζ₀` (= `u_pow_eq` at `u=1`). For `η=ζ₀` this gives `ση_unit=η_unit`
(`η_1` real); for `η=ζ₀⁻¹` it gives `ση_unit=ζ₀²·η_unit` (the `ζ`-asymmetry of `η_{-1}`). -/
lemma eta_unit_conj_of_real (hxa : (σ : 𝓞 K →+* 𝓞 K) x = -y) (hya : (σ : 𝓞 K →+* 𝓞 K) y = -x)
    {δ : 𝓞 K} {η_unit : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (η_unit : 𝓞 K) * (hζ.unit'.1 - 1) * δ ^ p) (hδ : δ ≠ 0)
    (hδreal : (σ : 𝓞 K →+* 𝓞 K) δ = δ) :
    (σ : 𝓞 K →+* 𝓞 K) (η_unit : 𝓞 K) = (η : 𝓞 K) ^ (p - 1) * (η_unit : 𝓞 K) * hζ.unit'.1 := by
  have := u_pow_eq hζ η hxa hya hgen hδ (u := 1) (by rw [hδreal, one_mul])
  simpa using this.symm

omit [IsCMField K] in
/-- **(C6) principal-generator extraction.** Under `𝔪 = (1)`, if the cascade ideal `𝔞(η)` is
principal — `𝔞(η) = (α)` — then `x + η·y = ε·π·αᵖ` for a unit `ε` (`π = ζ - 1`). From
`span{x+ηy} = 𝔞(η)ᵖ·𝔭 = (αᵖ·π)`. This turns Route A's principality (`routeA_a_principal`) into the
explicit generator identity that feeds Washington's real descent recombination. -/
lemma exists_gen_eq (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1)
    (hprin : (rootDivZetaSubOneDvdGcd hp hζ e hy η).IsPrincipal) :
    ∃ (α : 𝓞 K) (ε : (𝓞 K)ˣ), x + y * (η : 𝓞 K) = (ε : 𝓞 K) * (hζ.unit'.1 - 1) * α ^ p := by
  obtain ⟨α, hα⟩ := hprin
  have hspan : Ideal.span {x + y * (η : 𝓞 K)} = Ideal.span {α ^ p * (hζ.unit'.1 - 1)} := by
    rw [span_eq_a_pow_mul_p hp hζ e hy η hm, show (rootDivZetaSubOneDvdGcd hp hζ e hy η)
        = Ideal.span {α} from hα, Ideal.span_singleton_pow,
      Ideal.span_singleton_mul_span_singleton]
  rw [Ideal.span_singleton_eq_span_singleton] at hspan
  obtain ⟨u, hu⟩ := hspan
  refine ⟨α, u⁻¹, ?_⟩
  have hkey : (↑(u⁻¹) : 𝓞 K) * (hζ.unit'.1 - 1) * α ^ p
      = (↑(u⁻¹) : 𝓞 K) * ((x + y * (η : 𝓞 K)) * ↑u) := by rw [hu]; ring
  rw [hkey, mul_comm (x + y * (η : 𝓞 K)) ↑u, ← mul_assoc, Units.inv_mul, one_mul]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **(C6) conjugate generator.** Applying `σ` (conjugation) to the generator identity
`exists_gen_eq` (for real `x, y`): `x + η⁻¹·y = σ(ε)·(ζ⁻¹-1)·σ(α)ᵖ`. (`σ` fixes `x, y`, sends
`↑η ↦ ↑η⁻¹` and `ζ ↦ ζ⁻¹`.) This is the conjugate factor of Washington's recombination. -/
lemma conj_gen (hx : (σ : 𝓞 K →+* 𝓞 K) x = x) (hy_real : (σ : 𝓞 K →+* 𝓞 K) y = y)
    {α : 𝓞 K} {ε : (𝓞 K)ˣ}
    (hgen : x + y * (η : 𝓞 K) = (ε : 𝓞 K) * (hζ.unit'.1 - 1) * α ^ p) :
    x + y * ((η_inv η) : 𝓞 K)
      = (σ : 𝓞 K →+* 𝓞 K) (ε : 𝓞 K) * ((hζ.unit'⁻¹).1 - 1) * ((σ : 𝓞 K →+* 𝓞 K) α) ^ p := by
  have h := congrArg (σ : 𝓞 K →+* 𝓞 K) hgen
  rw [map_add, map_mul, map_mul, map_mul, map_pow, map_sub, map_one, hx, hy_real,
    sigma_unit hζ, sigma_eta η] at h
  exact h

omit [IsCMField K] in
lemma a_ne_zero (hz : ¬ hζ.unit'.1 - 1 ∣ z) :
    rootDivZetaSubOneDvdGcd hp hζ e hy η ≠ 0 := by
  intro h
  have hpri : Fact p.Prime := inferInstance
  have h_spec := root_div_zeta_sub_one_dvd_gcd_spec hp hζ e hy η
  dsimp only at h_spec
  have hc : divZetaSubOneDvdGcd hp hζ e hy η = 0 := by
    rw [← h_spec, h, zero_pow hpri.out.ne_zero]
  have h_mul : gcd (Ideal.span {x}) (Ideal.span {y}) *
    divZetaSubOneDvdGcd hp hζ e hy η * Ideal.span {hζ.unit'.1 - 1} = 0 := by
    rw [hc, mul_zero, zero_mul]
  simp only [IsPrimitiveRoot.coe_unit'] at h_mul
  rw [m_mul_c_mul_p hp hζ e hy η] at h_mul
  have h_not : Ideal.span {x + y * (η : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact x_plus_y_mul_ne_zero hp hζ e hz η
  exact h_not h_mul

omit [IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Class-group core of Route A's (C2).** If `(A·(b))ᵖ = ((a)·B)ᵖ` (integral ideals, `a,b ≠ 0`)
then `[A] = [B]` in the class group: by `p`-th-root uniqueness `A·(b) = (a)·B`, which is exactly the
`mk0_eq_mk0_iff` witness. (The descent supplies this from `u = wᵖ` after cross-multiplying and
cancelling the `𝔭` factors — see `span_eq_a_pow_mul_p`.) -/
lemma mk0_eq_of_pow_mul_eq {A B : Ideal (𝓞 K)} (hA : A ≠ 0) (hB : B ≠ 0)
    {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (A * Ideal.span {b}) ^ p = (Ideal.span {a} * B) ^ p) :
    ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_iff_ne_zero.mpr hA⟩
      = ClassGroup.mk0 ⟨B, mem_nonZeroDivisors_iff_ne_zero.mpr hB⟩ := by
  have heq : A * Ideal.span {b} = Ideal.span {a} * B :=
    pow_left_injective (Fact.out : Nat.Prime p).ne_zero h
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨b, a, hb, ha, by rw [mul_comm (Ideal.span {b}) A]; exact heq⟩

omit [NumberField K] [IsCMField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **(C2) span step (B-ii).** From the `𝓞 K` element identity `u₀·(x+y·η)·bᵖ = aᵖ·(x+y·η⁻¹)`
(`u₀` a unit — here `u₀ = -ζ⁻¹`), taking ideal spans (the unit is absorbed, `span{u₀·c} = span{c}`)
yields the cross-multiplied span identity `heq` consumed by `a_class_eq_of_cross_mul`. -/
lemma heq_of_unit_cross_mul {u₀ : (𝓞 K)ˣ} {a b : 𝓞 K}
    (h : (u₀ : 𝓞 K) * (x + y * (η : 𝓞 K)) * b ^ p = a ^ p * (x + y * ((η_inv η) : 𝓞 K))) :
    Ideal.span {x + y * (η : 𝓞 K)} * Ideal.span {b} ^ p
      = Ideal.span {a} ^ p * Ideal.span {x + y * ((η_inv η) : 𝓞 K)} := by
  rw [show Ideal.span {x + y * (η : 𝓞 K)} * Ideal.span {b} ^ p
        = Ideal.span {(x + y * (η : 𝓞 K)) * b ^ p} by
        rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton],
    show Ideal.span {a} ^ p * Ideal.span {x + y * ((η_inv η) : 𝓞 K)}
        = Ideal.span {a ^ p * (x + y * ((η_inv η) : 𝓞 K))} by
        rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton],
    Ideal.span_singleton_eq_span_singleton]
  exact ⟨u₀, by rw [← h]; ring⟩

omit [IsCMField K] in
/-- **Span-manipulation core of Route A's (C2) bridge.** Given the cross-multiplied span identity
`(x+y·η)·(b)ᵖ = (a)ᵖ·(x+y·η⁻¹)` (which the descent gets from `u = wᵖ`, `w = a/b`, after clearing the
unit `-ζ⁻¹`), substitute `span_eq_a_pow_mul_p` on both factors, cancel the shared `𝔭`, and conclude
`[𝔞 η] = [𝔞 η⁻¹]` via `mk0_eq_of_pow_mul_eq`. -/
lemma a_class_eq_of_cross_mul (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1)
    {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : Ideal.span {x + y * (η : 𝓞 K)} * Ideal.span {b} ^ p
         = Ideal.span {a} ^ p * Ideal.span {x + y * ((η_inv η) : 𝓞 K)}) :
    ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp hζ e hy η,
        mem_nonZeroDivisors_iff_ne_zero.mpr (a_ne_zero hp hζ e hy η hz)⟩
      = ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η),
        mem_nonZeroDivisors_iff_ne_zero.mpr (a_ne_zero hp hζ e hy (η_inv η) hz)⟩ := by
  rw [span_eq_a_pow_mul_p hp hζ e hy η hm,
      span_eq_a_pow_mul_p hp hζ e hy (η_inv η) hm] at heq
  have hcancel : rootDivZetaSubOneDvdGcd hp hζ e hy η ^ p * Ideal.span {b} ^ p
      = Ideal.span {a} ^ p * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η) ^ p := by
    apply mul_right_cancel₀ (p_ne_zero hζ)
    calc rootDivZetaSubOneDvdGcd hp hζ e hy η ^ p * Ideal.span {b} ^ p
            * Ideal.span {hζ.unit'.1 - 1}
        = rootDivZetaSubOneDvdGcd hp hζ e hy η ^ p * Ideal.span {hζ.unit'.1 - 1}
            * Ideal.span {b} ^ p := by ring
      _ = Ideal.span {a} ^ p * (rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η) ^ p
            * Ideal.span {hζ.unit'.1 - 1}) := heq
      _ = Ideal.span {a} ^ p * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η) ^ p
            * Ideal.span {hζ.unit'.1 - 1} := by ring
  rw [← mul_pow, ← mul_pow] at hcancel
  exact mk0_eq_of_pow_mul_eq (a_ne_zero hp hζ e hy η hz)
    (a_ne_zero hp hζ e hy (η_inv η) hz) ha hb hcancel

/-- The class group element corresponding to the ideal `𝔞 η`. -/
noncomputable def bClass (hp : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (η : nthRootsFinset p (1 : 𝓞 K)) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp hζ e hy η,
    mem_nonZeroDivisors_iff_ne_zero.mpr (a_ne_zero hp hζ e hy η hz)⟩

lemma conj_b_class (hp : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hx : σ x = x) (hy_real : σ y = y) :
    CyclotomicNT.classGroupMapEquiv σ (bClass hp hζ e hy hz η) =
      bClass hp hζ e hy hz (η_inv η) := by
  dsimp [bClass]
  rw [CyclotomicNT.classGroupMapEquiv_mk0]
  congr 1
  apply Subtype.ext
  simp only [CyclotomicNT.idealMapEquiv_coe]
  exact conj_a hp hζ e hy η hx hy_real (conj_i η hx hy_real)

/-- **The (C2) quotient fact, `b = σ_*(b)`**, from the cross-multiplied span identity: combining
`a_class_eq_of_cross_mul` (`[𝔞 η] = [𝔞 η⁻¹]`) with `conj_b_class` (`σ_*[𝔞 η] = [𝔞 η⁻¹]`). This is
exactly the `h_quot` hypothesis consumed by `B1_principal` — so once the descent supplies the
cross-mul identity (from `u = wᵖ`), `𝔞(ζ)` is principal. -/
lemma quotient_principal_of_cross_mul (hx : σ x = x) (hy_real : σ y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) {a b : 𝓞 K} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : Ideal.span {x + y * (η : 𝓞 K)} * Ideal.span {b} ^ p
         = Ideal.span {a} ^ p * Ideal.span {x + y * ((η_inv η) : 𝓞 K)}) :
    bClass hp hζ e hy hz η = CyclotomicNT.classGroupMapEquiv σ (bClass hp hζ e hy hz η) := by
  rw [conj_b_class hp hζ e hy hz η hx hy_real]
  exact a_class_eq_of_cross_mul hp hζ e hy hz η hm ha hb heq

omit [IsCMField K] in
lemma b_pow_p_eq_one (hp : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (η : nthRootsFinset p (1 : 𝓞 K))
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    bClass hp hζ e hy hz η ^ p = 1 := by
  dsimp [bClass]
  rw [← map_pow]
  rw [ClassGroup.mk0_eq_one_iff]
  exact a_pow_principal hp hζ e hy η hm

end CaseIIVandiverDescent

namespace CaseIIVandiverDescent

open NumberField Ideal Polynomial NumberField.IsCMField NumberField.Units

/-- **Step (3): `J_a` is principal.** Combining `J_conj_fixed` (conjugation-fixed),
`J_coprime_p` (coprime to `(p)`), and `J_pow_principal` (`J_aᵖ` principal, under `𝔪 = (1)`)
through the proved `CyclotomicNT.isPrincipal_of_conjFixed_of_pow` (which discharges principality
from `p ∤ h⁺`), the real product ideal `J_a = 𝔞(η)·𝔞(η⁻¹)` is principal. Specialized to
`K = CyclotomicField p ℚ`, since the principality engine is stated there. The `𝔪 = (1)`
hypothesis (`hm`) is carried from `J_pow_principal` and must be discharged when wiring the full
descent. -/
lemma J_principal {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hvand : IsVandiverPrime p)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (η : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)))
    (hx : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x)
    (hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1)
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη' : η_inv η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    (rootDivZetaSubOneDvdGcd hp hζ e hy η
      * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η)).IsPrincipal := by
  have hp2 : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hp)
  exact CyclotomicNT.isPrincipal_of_conjFixed_of_pow hp2 hvand
    (J_conj_fixed hp hζ e hy η hx hy_real)
    (J_coprime_p hp hζ e hy η hx hy_real hη hη')
    (J_pow_principal hp hζ e hy η hx hy_real hm)

/-- **`𝔞₀` is principal** (`η₀ = 1` case, the `x+y` factor). The `𝔭`-coprime part of `𝔞(η₀)` is
conjugation-fixed (`a_zero_conj_fixed`), coprime to `(p)` (`a_zero_coprime_p`), with `𝔞₀ᵖ` principal
(`a_zero_pow_principal`, under `𝔪 = (1)`); `p ∤ h⁺` makes it principal. This is the missing
principality for the §9.1 recombination's smaller-solution `z'` factor — no real-unit Kummer's
Lemma, no `p`-adic `L`, just the same reflection engine as `J_principal`. -/
lemma a_zero_principal {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hvand : IsVandiverPrime p)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (hx : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x)
    (hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    (aEtaZeroDvdPPow hp hζ e hy).IsPrincipal := by
  have hp2 : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hp)
  exact CyclotomicNT.isPrincipal_of_conjFixed_of_pow hp2 hvand
    (a_zero_conj_fixed hp hζ e hy hx hy_real)
    (a_zero_coprime_p hp hζ e hy hz)
    (a_zero_pow_principal hp hζ e hy hm)

/-- **`𝔞(η₀)` is principal.** `𝔞(η₀) = 𝔭^m·𝔞₀` with `𝔭 = (π)` and `𝔞₀` principal
(`a_zero_principal`), so `𝔞(η₀) = (π^m·γ₀)`. -/
lemma a_eta_zero_principal {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hvand : IsVandiverPrime p)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (hx : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x)
    (hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    (rootDivZetaSubOneDvdGcd hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy)).IsPrincipal := by
  obtain ⟨γ₀, hγ₀⟩ := (a_zero_principal hp hvand hζ e hy hz hx hy_real hm).principal
  have hγ₀' : aEtaZeroDvdPPow hp hζ e hy = Ideal.span {γ₀} := hγ₀
  exact ⟨⟨(hζ.unit'.1 - 1) ^ m * γ₀, by
    simp only [IsPrimitiveRoot.coe_unit']
    rw [← a_eta_zero_dvd_p_pow_spec hp hζ e hy, hγ₀', Ideal.span_singleton_pow,
        Ideal.span_singleton_mul_span_singleton]⟩⟩

/-- **(C6 Stage 2) anti-conjugate `𝔞₀` is conjugation-fixed** (`σ(𝔞 η₀) = 𝔞 η₀` directly from
`conj_a_antiConj`, then cancel `𝔭^m`). Mirror of `a_zero_conj_fixed` for anti-conjugate
solutions. -/
lemma a_zero_conj_fixed_antiConj {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (hxa : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = -y)
    (hya : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = -x) :
    Ideal.map (ringOfIntegersComplexConj (CyclotomicField p ℚ)
        : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ))
        (aEtaZeroDvdPPow hp hζ e hy)
      = aEtaZeroDvdPPow hp hζ e hy := by
  have hfix : Ideal.map (ringOfIntegersComplexConj (CyclotomicField p ℚ)
        : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ))
        (rootDivZetaSubOneDvdGcd hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy))
      = rootDivZetaSubOneDvdGcd hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy) :=
    conj_a_antiConj hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy) hxa hya
      (sigma_i_antiConj (zetaSubOneDvdRoot hp hζ e hy) hxa hya)
  have key := congrArg (Ideal.map (ringOfIntegersComplexConj (CyclotomicField p ℚ)
    : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ))) (a_eta_zero_dvd_p_pow_spec hp hζ e hy)
  simp only [← IsPrimitiveRoot.coe_unit'] at key
  rw [Ideal.map_mul, Ideal.map_pow, map_sigma_p hζ, hfix,
    ← a_eta_zero_dvd_p_pow_spec hp hζ e hy] at key
  exact mul_left_cancel₀ (pow_ne_zero m (p_ne_zero hζ)) key

/-- **(C6 Stage 2) anti-conjugate `𝔞₀` is principal** (`p∤h⁺`; conj-fixed + coprime-`(p)` + `𝔞₀ᵖ`
principal). Mirror of `a_zero_principal`. -/
lemma a_zero_antiConj_principal {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hvand : IsVandiverPrime p)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (hxa : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = -y)
    (hya : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = -x)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    (aEtaZeroDvdPPow hp hζ e hy).IsPrincipal := by
  have hp2 : 2 < p := lt_of_le_of_ne (Fact.out : Nat.Prime p).two_le (Ne.symm hp)
  exact CyclotomicNT.isPrincipal_of_conjFixed_of_pow hp2 hvand
    (a_zero_conj_fixed_antiConj hp hζ e hy hxa hya)
    (a_zero_coprime_p hp hζ e hy hz)
    (a_zero_pow_principal hp hζ e hy hm)

/-- **`π^{pm+1} ∣ (x + y·η₀)`** — the high cascade factor's `π`-valuation,
    **conjugation-independent**
(holds for real *and* anti-conjugate solutions). Pure ideal structure: `span{x+y·η₀} = 𝔞(η₀)ᵖ·𝔭`
(`span_eq_a_pow_mul_p`) and `𝔞(η₀) = 𝔭^m·𝔞₀` (`a_eta_zero_dvd_p_pow_spec`) give
`span{x+y·η₀} = 𝔭^{pm+1}·𝔞₀ᵖ`, so `𝔭^{pm+1} ∣ span{x+y·η₀}`, i.e. `π^{pm+1} ∣ (x+y·η₀)`. No
principality, no `σ`-hypotheses — `η₀` is *defined* as the high root, so this needs no proof that
`η₀ = 1`. This is the divisibility feeding Stage 2's `p ∣ S` for the anti-conjugate recombination
(built around `A₀ = x + y·η₀`). -/
lemma pow_dvd_x_plus_eta_zero_y {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    (hζ.unit'.1 - 1) ^ (p * m + 1)
      ∣ (x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 (CyclotomicField p ℚ))) := by
  have hideal : Ideal.span {hζ.unit'.1 - 1} ^ (p * m + 1)
      ∣ Ideal.span {x + y * (zetaSubOneDvdRoot hp hζ e hy : 𝓞 (CyclotomicField p ℚ))} := by
    rw [span_eq_a_pow_mul_p hp hζ e hy (zetaSubOneDvdRoot hp hζ e hy) hm,
        ← a_eta_zero_dvd_p_pow_spec hp hζ e hy]
    have h : (Ideal.span {hζ.unit'.1 - 1} ^ m * aEtaZeroDvdPPow hp hζ e hy) ^ p
          * Ideal.span {hζ.unit'.1 - 1}
        = Ideal.span {hζ.unit'.1 - 1} ^ (p * m + 1) * (aEtaZeroDvdPPow hp hζ e hy) ^ p := by
      rw [mul_pow, ← pow_mul, pow_succ, mul_comm m p]; ring
    simp only [← IsPrimitiveRoot.coe_unit']
    rw [h]; exact dvd_mul_right _ _
  rw [Ideal.span_singleton_pow] at hideal
  rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_span_singleton] at hideal

/-- **`π^{pm+1} ∣ (x+y)`** for **real** solutions, where `η₀ = 1` (`eta_zero_eq_one`). Specializes
`pow_dvd_x_plus_eta_zero_y`. -/
lemma pow_dvd_x_plus_y {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (hx : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x)
    (hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1) :
    (hζ.unit'.1 - 1) ^ (p * m + 1) ∣ (x + y) := by
  have h := pow_dvd_x_plus_eta_zero_y hp hζ e hy hm
  rwa [eta_zero_eq_one hp hζ e hy hx hy_real, mul_one] at h

/-- **`η₀ = 1` from `π² ∣ (x+y)`** — the converse characterization (`η₀ = 1 ⟺ v_π(x+y) ≥ 2`).
`span{x+y} = 𝔞(1)ᵖ·𝔭`, so `𝔭² ∣ span{x+y}` cancels one `𝔭` to give `𝔭 ∣ 𝔞(1)ᵖ`, hence `𝔭 ∣ 𝔞(1)`
(`𝔭` prime), hence `1 = η₀` (`p_dvd_a_iff`). Conjugation-independent. This is the engine of the
anti-conjugate normalization: after replacing `(x,y) ↦ (ζᵏx, ζ⁻ᵏy)` so that `x+y` becomes the high
factor, this lemma certifies `η₀ = 1` for the normalized solution. -/
lemma eta_zero_eq_one_of_pi_sq_dvd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1)
    (hdvd : (hζ.unit'.1 - 1) ^ 2 ∣ (x + y)) :
    (zetaSubOneDvdRoot hp hζ e hy : 𝓞 (CyclotomicField p ℚ)) = 1 := by
  have hπ0 : hζ.unit'.1 - 1 ≠ 0 := hζ.unit'_coe.sub_one_ne_zero (Fact.out : Nat.Prime p).one_lt
  have hπspan0 : Ideal.span {hζ.unit'.1 - 1} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hπ0
  set η1 : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) :=
    ⟨1, one_mem_nthRootsFinset (Fact.out : Nat.Prime p).pos⟩ with hη1def
  have hcoe : (η1 : 𝓞 (CyclotomicField p ℚ)) = 1 := rfl
  have h2 : Ideal.span {hζ.unit'.1 - 1} ^ 2
      ∣ Ideal.span {x + y * (η1 : 𝓞 (CyclotomicField p ℚ))} := by
    rw [hcoe, mul_one, Ideal.span_singleton_pow, Ideal.dvd_iff_le,
        Ideal.span_singleton_le_span_singleton]
    exact hdvd
  rw [span_eq_a_pow_mul_p hp hζ e hy η1 hm, sq,
      mul_comm (rootDivZetaSubOneDvdGcd hp hζ e hy η1 ^ p)] at h2
  have h3 : Ideal.span {hζ.unit'.1 - 1} ∣ rootDivZetaSubOneDvdGcd hp hζ e hy η1 ^ p :=
    (mul_dvd_mul_iff_left hπspan0).mp h2
  have h4 : Ideal.span {hζ.unit'.1 - 1} ∣ rootDivZetaSubOneDvdGcd hp hζ e hy η1 :=
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').dvd_of_dvd_pow h3
  have h5 : η1 = zetaSubOneDvdRoot hp hζ e hy := (p_dvd_a_iff hp hζ e hy η1).mp h4
  rw [← h5, hcoe]

/-- For an odd prime `p`, every `p`-th root of unity `w` is an **even** power `ζ^{2k}` of `ζ`
(`2` is invertible mod `p`). The root-arithmetic core of the anti-conjugate normalization: it lets
us solve `ζ^{-2k} = η₀` for the shift `k` that turns `x+y` into the high cascade factor. -/
lemma exists_sq_pow_eq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {w : 𝓞 (CyclotomicField p ℚ)} (hw : w ^ p = 1) :
    ∃ k : ℕ, hζ.unit'.1 ^ (2 * k) = w := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨i, hi, hieq⟩ := hζ.unit'_coe.eq_pow_of_pow_eq_one hw
  have hporder : orderOf hζ.unit' = p := orderOf_units.symm.trans hζ.unit'_coe.eq_orderOf.symm
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have hnd : ¬ (p ∣ 2) := fun h =>
      hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring,
        Ne, ZMod.natCast_eq_zero_iff]
    exact hnd
  set a : ZMod p := (2 : ZMod p)⁻¹ * (i : ZMod p) with ha
  have key : hζ.unit' ^ (2 * a.val) = hζ.unit' ^ i := by
    rw [pow_eq_pow_iff_modEq, hporder, ← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id, ha, ← mul_assoc, mul_inv_cancel₀ h2ne, one_mul]
  refine ⟨a.val, ?_⟩
  calc hζ.unit'.1 ^ (2 * a.val) = ((hζ.unit' ^ (2 * a.val) : (𝓞 (CyclotomicField p ℚ))ˣ)
        : 𝓞 (CyclotomicField p ℚ)) := (Units.val_pow_eq_pow_val _ _).symm
    _ = ((hζ.unit' ^ i : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) :=
        congrArg Units.val key
    _ = hζ.unit'.1 ^ i := Units.val_pow_eq_pow_val _ _
    _ = w := hieq

lemma b_mul_conj_b_eq_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hvand : IsVandiverPrime p)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (η : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)))
    (hx : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x)
    (hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1)
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη' : η_inv η ≠ zetaSubOneDvdRoot hp hζ e hy) :
    bClass hp hζ e hy hz η * CyclotomicNT.classGroupMapEquiv
      (ringOfIntegersComplexConj (CyclotomicField p ℚ)) (bClass hp hζ e hy hz η) = 1 := by
  rw [conj_b_class hp hζ e hy hz η hx hy_real]
  have h_prod : bClass hp hζ e hy hz η * bClass hp hζ e hy hz (η_inv η) =
      ClassGroup.mk0 ⟨rootDivZetaSubOneDvdGcd hp hζ e hy η
        * rootDivZetaSubOneDvdGcd hp hζ e hy (η_inv η),
        mul_mem (mem_nonZeroDivisors_iff_ne_zero.mpr (a_ne_zero hp hζ e hy η hz))
                (mem_nonZeroDivisors_iff_ne_zero.mpr (a_ne_zero hp hζ e hy (η_inv η) hz))⟩ := by
    dsimp [bClass]
    rw [← map_mul]
    rfl
  rw [h_prod]
  rw [ClassGroup.mk0_eq_one_iff]
  exact J_principal hp hvand hζ e hy η hx hy_real hm hη hη'

lemma eq_one_of_pow_two_eq_one_of_pow_odd {G : Type*} [CommGroup G] {p : ℕ} (hp : Odd p)
    {b : G} (h2 : b ^ 2 = 1) (hp_pow : b ^ p = 1) : b = 1 := by
  rcases hp with ⟨k, rfl⟩
  have h : b ^ (2 * k + 1) = b := by
    rw [pow_add, pow_mul, h2, one_pow, one_mul, pow_one]
  rw [h] at hp_pow
  exact hp_pow

lemma b_sq_eq_one_of_quotient_principal {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hvand : IsVandiverPrime p)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (η : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)))
    (hx : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x)
    (hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1)
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη' : η_inv η ≠ zetaSubOneDvdRoot hp hζ e hy)
    (h_quot : bClass hp hζ e hy hz η = CyclotomicNT.classGroupMapEquiv
      (ringOfIntegersComplexConj (CyclotomicField p ℚ)) (bClass hp hζ e hy hz η)) :
    bClass hp hζ e hy hz η ^ 2 = 1 := by
  have h_mul := b_mul_conj_b_eq_one hp hvand hζ e hy hz η hx hy_real hm hη hη'
  rw [← h_quot] at h_mul
  rw [sq]
  exact h_mul

lemma B1_principal {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hvand : IsVandiverPrime p)
    [IsCMField (CyclotomicField p ℚ)] [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {x y z : 𝓞 (CyclotomicField p ℚ)} {ε : (𝓞 (CyclotomicField p ℚ))ˣ} {m : ℕ}
    (e : x ^ p + y ^ p = ε * ((hζ.unit'.1 - 1) ^ (m + 1) * z) ^ p)
    (hy : ¬ hζ.unit'.1 - 1 ∣ y) (hz : ¬ hζ.unit'.1 - 1 ∣ z)
    (η : nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)))
    (hx : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) x = x)
    (hy_real : (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) y = y)
    (hm : gcd (Ideal.span {x}) (Ideal.span {y}) = 1)
    (hη : η ≠ zetaSubOneDvdRoot hp hζ e hy)
    (hη' : η_inv η ≠ zetaSubOneDvdRoot hp hζ e hy)
    (h_quot : bClass hp hζ e hy hz η = CyclotomicNT.classGroupMapEquiv
      (ringOfIntegersComplexConj (CyclotomicField p ℚ)) (bClass hp hζ e hy hz η)) :
    bClass hp hζ e hy hz η = 1 := by
  have hpri : Fact p.Prime := inferInstance
  have hp_odd : Odd p := Nat.odd_iff.mpr (hpri.out.eq_two_or_odd.resolve_left hp)
  have h_sq := b_sq_eq_one_of_quotient_principal hp hvand hζ e hy hz η hx hy_real hm hη hη' h_quot
  have h_pow := b_pow_p_eq_one hp hζ e hy hz η hm
  exact eq_one_of_pow_two_eq_one_of_pow_odd hp_odd h_sq h_pow

end CaseIIVandiverDescent
