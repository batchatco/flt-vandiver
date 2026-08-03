import FltVandiver.CaseII95Core
import FltVandiver.Descent92Induction
import CyclotomicNT.CaseIKummer
import CyclotomicNT.BernoulliMod
import FltRegular.MayAssume.Lemmas
import Mathlib.NumberTheory.FLT.Basic

/-!
# The Washington Theorem 9.5 route, descent + engine (UNCOMMITTED MODULE)

The descent spine (the ℓ-invariant threaded through the §9.1 descent),
Lemmas 9.6/9.7 (the auxiliary-prime seeding), `caseII_95_top`, the
orientation-symmetry wrappers, and the certificate engines
`fermatLastTheoremFor_of_certs_95` / `_of_certs_95'`.

A per-prime FLT proof via this route needs only: the Boolean certificate
`vandiverCert p ℓ t (evenIndices p) = true`, the bound `ℓ < p² − p`
(`by norm_num`), and a Case I input — either `irrListCert` with `p − 3`
regular, or an `sgCert` auxiliary prime.
-/

namespace FltVandiver.Descent95

/-! ### The descent spine

The §9.1 descent with the `ℓ ∣ ξ` invariant threaded through: `descent_step_95`
runs the classical per-level machinery with `lemma_9_8_all` + `assumption_II_95`
at the eigenspace step, and re-establishes the invariant at the next level
(`ℓ ∣ ω + θ = η₀λ^{m′}ρ₀^p` forces `ℓ ∣ ρ₀` by CRT, and the new `ξ` is `ρ₀²`).
All witness data — including Vandiver at `p` — comes from the single
all-even-index `Q_i` certificate. -/

section Spine

open CyclotomicNT FltVandiver FltVandiver.QiCert FltVandiver.Descent92
open NumberField NumberField.IsCMField Polynomial UniqueFactorizationMonoid
open scoped NumberField

variable {p : ℕ} [hpri : Fact p.Prime] {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  [NumberField.IsCMField (CyclotomicField p ℚ)]

omit [IsCMField (CyclotomicField p ℚ)] in
/-- The reduction homs never kill `λ`. -/
theorem redHom_lambda0_ne_zero {ζ : CyclotomicField p ℚ}
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    {t' : ℕ} (hμ' : IsPrimitiveRoot (redRoot p ℓ t') p) :
    redHom hζ hμ' (lambda0 hζ) ≠ 0 := by
  have hlamdef : lambda0 hζ
      = (1 - hζ.toInteger) * (1 - hζ.toInteger ^ (p - 1)) := rfl
  rw [hlamdef, map_mul, map_sub, map_one, redHom_zeta, map_sub, map_one, map_pow,
    redHom_zeta]
  refine mul_ne_zero ?_ ?_
  · intro h0
    have h1 : redRoot p ℓ t' = 1 := by linear_combination -h0
    exact hμ'.ne_one (by omega) h1
  · intro h0
    have h1 : redRoot p ℓ t' ^ (p - 1) = 1 := by linear_combination -h0
    have h2 := Nat.le_of_dvd (by omega) ((hμ'.pow_eq_one_iff_dvd (p - 1)).mp h1)
    omega

omit hpri [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- Bridge: the units-level and `𝓞`-level complex conjugations agree. -/
theorem unitsComplexConj_val (u : (𝓞 (CyclotomicField p ℚ))ˣ) :
    ((unitsComplexConj (CyclotomicField p ℚ) u : (𝓞 (CyclotomicField p ℚ))ˣ)
        : 𝓞 (CyclotomicField p ℚ))
      = ringOfIntegersComplexConj (CyclotomicField p ℚ)
          ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
  apply NumberField.RingOfIntegers.ext
  rfl

omit hpri [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- A unit with conjugation-fixed value is a real unit. -/
theorem mem_realUnits_of_conjO_fixed {u : (𝓞 (CyclotomicField p ℚ))ˣ}
    (h : ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))) :
    u ∈ realUnits (CyclotomicField p ℚ) := by
  rw [← unitsComplexConj_eq_self_iff]
  ext
  rw [unitsComplexConj_val, h]

omit hpri [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- Conversely, real units have conjugation-fixed values. -/
theorem conjO_fixed_of_mem_realUnits {u : (𝓞 (CyclotomicField p ℚ))ˣ}
    (h : u ∈ realUnits (CyclotomicField p ℚ)) :
    ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = ((u : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
  rw [← unitsComplexConj_eq_self_iff] at h
  have h1 := congrArg (Units.val) h
  rw [unitsComplexConj_val] at h1
  exact h1

set_option maxHeartbeats 2000000 in -- heavy elaboration: exceeds the default heartbeat budget
/-- **The 9.5-route descent driver** (one level): the ℓ-data powers the
eigenspace step, and the invariant `ℓ ∣ ξ` is carried to the next level. -/
theorem descent_step_95 {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 3 < p) (hvand : IsVandiverPrime p)
    (hℓp : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    (hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1)
    (hℓξ : ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ S.ξ) :
    ∃ (S' : Situation92 hζ) (B₀ Brest : Ideal (𝓞 (CyclotomicField p ℚ))),
      ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ S'.ξ
      ∧ S'.m = 2 * S.m - p
      ∧ Ideal.span {S'.ξ} = B₀ ^ 2
      ∧ Ideal.span {S.ξ} = B₀ * Brest
      ∧ IsCoprime B₀ Brest
      ∧ Brest ≠ ⊤ := by
  classical
  have hp2 : 2 < p := by omega
  have hp5 : 5 ≤ p := by
    by_contra h
    push Not at h
    have hp4 : p = 4 := by omega
    have h2 := hpri.out
    rw [hp4] at h2
    exact absurd h2 (by decide)
  have hvand' : ¬ p ∣ Fintype.card (ClassGroup
      (𝓞 (maximalRealSubfield (CyclotomicField p ℚ)))) :=
    (Nat.Prime.coprime_iff_not_dvd hpri.out).mp hvand
  -- the B-decomposition
  obtain ⟨B, hB1, hB2, hBprod, hBpair⟩ := exists_factor_ideals S hp2
  have hpow : hζ.toInteger ^ p = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ))
      (CyclotomicField p ℚ)
    have ht : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
        hζ.toInteger = ζ := hζ.coe_toInteger
    rw [map_pow, map_one, ht]
    exact hζ.pow_eq_one
  have hmem : ∀ j : ℕ, hζ.toInteger ^ j
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
    intro j
    rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
      hpow, one_pow]
  have h1mem : (1 : 𝓞 (CyclotomicField p ℚ))
      ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) :=
    Polynomial.one_mem_nthRootsFinset hpri.out.pos
  have hpinj : ∀ i j : ℕ, i < p → j < p → i ≠ j
      → hζ.toInteger ^ i ≠ hζ.toInteger ^ j := by
    intro i j hi hj hne heq
    exact hne (hζ.toInteger_isPrimitiveRoot.pow_inj hi hj heq)
  have hne10 : hζ.toInteger ^ 1 ≠ (1 : 𝓞 (CyclotomicField p ℚ)) := by
    intro h
    exact hpinj 1 0 (by omega) (by omega) (by omega) (by rw [pow_zero]; exact h)
  have hBeq : ∀ j : ℕ, 0 < j → j < p →
      Ideal.span {S.ω + hζ.toInteger ^ j * S.θ}
        = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}
          * (B (hζ.toInteger ^ j)) ^ p := by
    intro j hj0 hjp
    have h1 := hB1 (hζ.toInteger ^ j) (hmem j)
    rw [if_neg (by
      intro h
      exact hpinj j 0 hjp (by omega) (by omega) (by rw [pow_zero]; exact h)),
      pow_one] at h1
    exact h1
  have hred : ∀ j : ℕ, 0 < j → j < p →
      hζ.toInteger ^ (j * (p - 1)) = hζ.toInteger ^ (p - j) := by
    intro j hj0 hjp
    refine toInteger_pow_eq_of_mod hζ ?_
    have h2 : j * (p - 1) = j * p - j := by
      zify [show 1 ≤ p from by omega, show j ≤ j * p from
        Nat.le_mul_of_pos_right j (by omega)]
      ring
    have h3 : j * p - j = (j - 1) * p + (p - j) := by
      zify [show 1 ≤ j from hj0, show j ≤ j * p from
        Nat.le_mul_of_pos_right j (by omega), show j ≤ p from by omega]
      ring
    rw [h2, h3, Nat.mul_add_mod_self_right]
  have hc1 : (1 : ℕ).Coprime p := Nat.coprime_one_left p
  have hc2 : (2 : ℕ).Coprime p :=
    (Nat.coprime_primes Nat.prime_two hpri.out).mpr (by omega)
  have hred1 : hζ.toInteger ^ (1 * (p - 1)) = hζ.toInteger ^ (p - 1) := by
    rw [one_mul]
  have hred2 : hζ.toInteger ^ (2 * (p - 1)) = hζ.toInteger ^ (p - 2) :=
    hred 2 (by omega) (by omega)
  -- step 3 at a = 1 and a = 2
  obtain ⟨ηa, ρa, hηareal, heqa, heqma⟩ := step3_packaged S hp2 hvand hc1
    (Ba := B (hζ.toInteger ^ 1)) (Bma := B (hζ.toInteger ^ (p - 1)))
    (hBeq 1 (by omega) (by omega))
    (by rw [hred1]; exact hBeq (p - 1) (by omega) (by omega))
    (hB2 _ (hmem 1)) (hB2 _ (hmem (p - 1)))
  obtain ⟨ηb, ρb, hηbreal, heqb, heqmb⟩ := step3_packaged S hp2 hvand hc2
    (Ba := B (hζ.toInteger ^ 2)) (Bma := B (hζ.toInteger ^ (p - 2)))
    (hBeq 2 (by omega) (by omega))
    (by rw [hred2]; exact hBeq (p - 2) (by omega) (by omega))
    (hB2 _ (hmem 2)) (hB2 _ (hmem (p - 2)))
  -- step 1
  obtain ⟨η₀, ρ₀, hη₀real, hρ₀real, heq0⟩ := step1_real_decomposition S hp2 hvand
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  have h𝔭ne : Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}
      ≠ (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hπprime.ne_zero
  have hB₀eq : Ideal.span {S.ω + S.θ}
      = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))})
          ^ (2 * S.m - (p - 1)) * (B 1) ^ p := by
    have h1 := hB1 1 h1mem
    rwa [if_pos (rfl : (1 : 𝓞 (CyclotomicField p ℚ)) = 1), one_mul] at h1
  have hspanρ₀ : Ideal.span {ρ₀} = B 1 := by
    have h1 : Ideal.span {S.ω + S.θ}
        = (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))})
            ^ (2 * S.m - (p - 1)) * (Ideal.span {ρ₀}) ^ p := by
      rw [heq0]
      have h2 : (lambda0 hζ) ^ (S.m - (p - 1) / 2)
          = (-hζ.toInteger ^ (p - 1)) ^ (S.m - (p - 1) / 2)
            * ((1 - hζ.toInteger) ^ (2 * S.m - (p - 1))) := by
        rw [lambda0_eq_unit_mul_sq hζ hp2, mul_pow, ← pow_mul]
        congr 2
        have h4 : 2 ∣ p - 1 := by
          have hodd := hpri.out.odd_of_ne_two (by omega)
          rw [Nat.odd_iff] at hodd
          omega
        have hub : p * (p - 1) ≤ 2 * S.m := by
          have h6 : 2 ∣ p * (p - 1) := Dvd.dvd.mul_left h4 p
          have h7 := S.hm
          omega
        have h8 : (p - 1) / 2 ≤ S.m := by
          refine le_trans ?_ S.hm
          refine Nat.div_le_div_right ?_
          exact Nat.le_mul_of_pos_left _ (by omega)
        have h9 : 2 * ((p - 1) / 2) = p - 1 := by omega
        omega
      have hassoc : Associated
          ((1 - hζ.toInteger) ^ (2 * S.m - (p - 1)) * ρ₀ ^ p
            : 𝓞 (CyclotomicField p ℚ))
          (((η₀ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * (lambda0 hζ) ^ (S.m - (p - 1) / 2) * ρ₀ ^ p) := by
        rw [h2]
        have hu : IsUnit ((-hζ.toInteger ^ (p - 1) : 𝓞 (CyclotomicField p ℚ))
            ^ (S.m - (p - 1) / 2)) := by
          refine IsUnit.pow _ (IsUnit.neg ?_)
          rw [show (hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
              = ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            from rfl]
          exact (hζ.unit'.isUnit).pow _
        obtain ⟨vu, hvu⟩ := hu
        refine ⟨η₀ * vu, ?_⟩
        rw [Units.val_mul, ← hvu]
        ring
      rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc,
        ← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow,
        Ideal.span_singleton_pow]
    rw [h1] at hB₀eq
    have h5 : (Ideal.span {ρ₀} : Ideal (𝓞 (CyclotomicField p ℚ))) ^ p
        = (B 1) ^ p :=
      mul_left_cancel₀ (a := (Ideal.span {(1 - hζ.toInteger
        : 𝓞 (CyclotomicField p ℚ))}) ^ (2 * S.m - (p - 1)))
        (pow_ne_zero _ h𝔭ne) hB₀eq
    exact pow_left_injective hpri.out.ne_zero h5
  -- spans of the step-3 witnesses
  have hspanρa : Ideal.span {ρa} = B (hζ.toInteger ^ 1) :=
    span_rho_eq_of_step3 S hp2 (a := 1)
      (by intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega))
      heqa (hBeq 1 (by omega) (by omega))
  have hspanρac : Ideal.span {ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa}
      = B (hζ.toInteger ^ (p - 1)) :=
    span_rho_eq_of_step3 S hp2 (a := p - 1)
      (by intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega))
      (by rw [← hred1]; exact heqma)
      (hBeq (p - 1) (by omega) (by omega))
  have hspanρb : Ideal.span {ρb} = B (hζ.toInteger ^ 2) :=
    span_rho_eq_of_step3 S hp2 (a := 2)
      (by intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega))
      heqb (hBeq 2 (by omega) (by omega))
  have hspanρbc : Ideal.span {ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb}
      = B (hζ.toInteger ^ (p - 2)) :=
    span_rho_eq_of_step3 S hp2 (a := p - 2)
      (by intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega))
      (by rw [← hred2]; exact heqmb)
      (hBeq (p - 2) (by omega) (by omega))
  have hπnot : ∀ (x : 𝓞 (CyclotomicField p ℚ)) (j : ℕ),
      Ideal.span {x} = B (hζ.toInteger ^ j)
      → hζ.toInteger ^ j ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))
      → ¬ (1 - hζ.toInteger) ∣ x := by
    intro x j hspan hjmem hdvd
    refine hB2 _ hjmem ?_
    rw [← hspan, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
    exact hdvd
  have hπρa := hπnot ρa 1 hspanρa (hmem 1)
  have hπρac := hπnot _ (p - 1) hspanρac (hmem (p - 1))
  have hπρb := hπnot ρb 2 hspanρb (hmem 2)
  have hπρbc := hπnot _ (p - 2) hspanρbc (hmem (p - 2))
  have hpairs : ∀ i j : ℕ, i < p → j < p → i ≠ j →
      IsCoprime (B (hζ.toInteger ^ i)) (B (hζ.toInteger ^ j)) := by
    intro i j hi hj hne
    exact hBpair _ (hmem i) _ (hmem j) (hpinj i j hi hj hne)
  -- ===== the ℓ-data block: Lemma 9.8 and Assumption II from the certificate =====
  have hneab12 : hζ.toInteger ^ 1 ≠ hζ.toInteger ^ 2 :=
    hpinj 1 2 (by omega) (by omega) (by omega)
  have hpab12 : ¬ p ∣ (1 + 2) := by
    intro h
    exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  have hpd1 : ¬ p ∣ 1 := fun h =>
    absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hpd2 : ¬ p ∣ 2 := fun h =>
    absurd (Nat.le_of_dvd (by omega) h) (by omega)
  -- Bezout coprimality of ω, θ
  have hcopE : ∃ r s : 𝓞 (CyclotomicField p ℚ), r * S.ω + s * S.θ = 1 := by
    obtain ⟨r, s, hrs⟩ := (Ideal.isCoprime_span_singleton_iff _ _).mp S.hωθ
    exact ⟨r, s, hrs⟩
  -- the paired equations at EVERY index prime to p
  have heqs : ∀ a : ℕ, ¬ p ∣ a → ∃ (ηc : (𝓞 (CyclotomicField p ℚ))ˣ)
      (ρc ρc' : 𝓞 (CyclotomicField p ℚ)),
      S.ω + hζ.toInteger ^ a * S.θ
        = (1 - hζ.toInteger ^ a)
          * ((ηc : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρc ^ p ∧
      S.ω + hζ.toInteger ^ (a * (p - 1)) * S.θ
        = (1 - hζ.toInteger ^ (a * (p - 1)))
          * ((ηc : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρc' ^ p
      := by
    intro a hpa
    have hamod0 : 0 < a % p :=
      Nat.pos_of_ne_zero (fun h => hpa (Nat.dvd_of_mod_eq_zero h))
    have hamodlt : a % p < p := Nat.mod_lt _ hpri.out.pos
    have hacop : a.Coprime p :=
      ((Nat.Prime.coprime_iff_not_dvd hpri.out).mpr hpa).symm
    have hza : hζ.toInteger ^ a = hζ.toInteger ^ (a % p) :=
      toInteger_pow_eq_of_mod hζ (Nat.mod_mod_of_dvd a dvd_rfl).symm
    have hzam : hζ.toInteger ^ (a * (p - 1)) = hζ.toInteger ^ (p - a % p) := by
      have h1 : hζ.toInteger ^ (a * (p - 1))
          = hζ.toInteger ^ ((a % p) * (p - 1)) :=
        toInteger_pow_eq_of_mod hζ
          (Nat.ModEq.mul_right (p - 1) (Nat.mod_modEq a p).symm)
      rw [h1]
      exact hred (a % p) hamod0 hamodlt
    obtain ⟨ηc, ρc, _, heqc, heqmc⟩ := step3_packaged S hp2 hvand hacop
      (Ba := B (hζ.toInteger ^ (a % p)))
      (Bma := B (hζ.toInteger ^ (p - a % p)))
      (by rw [hza]; exact hBeq (a % p) hamod0 hamodlt)
      (by rw [hzam]; exact hBeq (p - a % p) (by omega) (by omega))
      (hB2 _ (hmem (a % p))) (hB2 _ (hmem (p - a % p)))
    exact ⟨ηc, ρc, ringOfIntegersComplexConj (CyclotomicField p ℚ) ρc,
      heqc, heqmc⟩
  -- the product decomposition and hom-nonvanishing of its unit part
  have hprod := prod_factorization S hp2
  have hm0 : S.m ≠ 0 := by
    have h1 := S.hm
    have h2 : 5 * 4 / 2 ≤ p * (p - 1) / 2 :=
      Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
    omega
  have hWall : ∀ (t' : ℕ) (hμ' : IsPrimitiveRoot (redRoot p ℓ t') p),
      redHom hζ hμ'
        (((S.η : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
          * (lambda0 hζ) ^ S.m) ≠ 0 := by
    intro t' hμ' h0
    rw [map_mul, map_pow] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact (S.η.isUnit.map (redHom hζ hμ')).ne_zero h1
    · exact redHom_lambda0_ne_zero hζ hp2 hμ'
        ((pow_eq_zero_iff hm0).mp h1)
  -- the ℓ-invariant climbs to ω + θ
  have hsum : ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ (S.ω + S.θ) :=
    lemma_9_8_all hζ hp2 hℓp hμ hℓk hkeven (i₀ := 2) (by decide) (by omega)
      (by omega) (hQall 2 (by decide) (by omega) (by omega))
      hprod hWall hcopE heqs hℓξ
  -- Assumption II from the ℓ-data
  obtain ⟨v, hvmem, hveq⟩ := assumption_II_95 hζ hp2 hℓp hμ hℓk hkeven hQall
    hsum hcopE hpd1 hpd2 (mem_realUnits_of_conjO_fixed hηareal)
    (mem_realUnits_of_conjO_fixed hηbreal) heqa heqb
  -- square it into the shape the iterated equation wants
  have hwp : (v ^ 2) ^ p = ηa ^ 2 * (ηb ^ 2)⁻¹ := by
    rw [hveq, mul_pow, mul_comm (ηb ^ 2) ((v ^ p) ^ 2), mul_assoc,
      mul_inv_cancel, mul_one, ← pow_mul, ← pow_mul, mul_comm p 2]
  have hvfix := conjO_fixed_of_mem_realUnits hvmem
  have hwreal : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      ((v ^ 2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = ((v ^ 2 : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
    rw [Units.val_pow_eq_pow_val, map_pow, hvfix]
  -- the iterated equation
  obtain ⟨η₁, hη₁eq⟩ := iterated_equation S hp hc1 hc2 hpab12 hneab12
    heqa heqma heqb heqmb heq0 hwp
  -- the invariant descends to ρ₀
  have hℓρ₀ : ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ ρ₀ := by
    apply dvd_of_forall_redHom_eq_zero hζ hp2 hμ
    intro t' hμ'
    have h0 := redHom_eq_zero_of_dvd hζ hμ' hsum
    rw [heq0, map_mul, map_mul, map_pow, map_pow] at h0
    have hm0' : S.m - (p - 1) / 2 ≠ 0 := by
      have h1 := S.hm
      have h2 : 2 ∣ p - 1 := by
        have hodd := hpri.out.odd_of_ne_two (by omega)
        rw [Nat.odd_iff] at hodd
        omega
      have h3 : p * ((p - 1) / 2) = p * (p - 1) / 2 :=
        (Nat.mul_div_assoc p h2).symm
      have h4 : 5 * ((p - 1) / 2) ≤ p * ((p - 1) / 2) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 ((η₀.isUnit.map (redHom hζ hμ')).ne_zero)
      · exact absurd ((pow_eq_zero_iff hm0').mp h2)
          (redHom_lambda0_ne_zero hζ hp2 hμ')
    · exact (pow_eq_zero_iff hpri.out.ne_zero).mp h1
  -- the coprimality feeds for the next situation
  have hprodspan : ∀ x y : 𝓞 (CyclotomicField p ℚ),
      Ideal.span ({x * y} : Set (𝓞 (CyclotomicField p ℚ)))
        = Ideal.span {x} * Ideal.span {y} :=
    fun x y => (Ideal.span_singleton_mul_span_singleton x y).symm
  have hcab : IsCoprime
      (Ideal.span {ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa})
      (Ideal.span {ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb}) := by
    rw [hprodspan, hprodspan, hspanρa, hspanρac, hspanρb, hspanρbc]
    refine IsCoprime.mul_left ?_ ?_ <;> refine IsCoprime.mul_right ?_ ?_
    · exact hpairs 1 2 (by omega) (by omega) (by omega)
    · exact hpairs 1 (p - 2) (by omega) (by omega) (by omega)
    · exact hpairs (p - 1) 2 (by omega) (by omega) (by omega)
    · exact hpairs (p - 1) (p - 2) (by omega) (by omega) (by omega)
  have hsq0 : Ideal.span ({ρ₀ ^ 2} : Set (𝓞 (CyclotomicField p ℚ)))
      = (B 1) ^ 2 := by
    rw [← Ideal.span_singleton_pow, hspanρ₀]
  have hB1as : B 1 = B (hζ.toInteger ^ 0) := by
    rw [pow_zero]
  have hca0 : IsCoprime
      (Ideal.span {ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa})
      (Ideal.span ({ρ₀ ^ 2} : Set (𝓞 (CyclotomicField p ℚ)))) := by
    rw [hprodspan, hspanρa, hspanρac, hsq0, hB1as]
    refine IsCoprime.mul_left ?_ ?_ <;> refine IsCoprime.pow_right ?_
    · exact hpairs 1 0 (by omega) (by omega) (by omega)
    · exact hpairs (p - 1) 0 (by omega) (by omega) (by omega)
  have hcb0 : IsCoprime
      (Ideal.span {ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb})
      (Ideal.span ({ρ₀ ^ 2} : Set (𝓞 (CyclotomicField p ℚ)))) := by
    rw [hprodspan, hspanρb, hspanρbc, hsq0, hB1as]
    refine IsCoprime.mul_left ?_ ?_ <;> refine IsCoprime.pow_right ?_
    · exact hpairs 2 0 (by omega) (by omega) (by omega)
    · exact hpairs (p - 2) 0 (by omega) (by omega) (by omega)
  have hπprodA : ¬ (1 - hζ.toInteger)
      ∣ (ρa * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρa) := by
    intro h
    rcases hπprime.dvd_mul.mp h with h1 | h1
    · exact hπρa h1
    · exact hπρac h1
  have hπprodB : ¬ (1 - hζ.toInteger)
      ∣ (ρb * ringOfIntegersComplexConj (CyclotomicField p ℚ) ρb) := by
    intro h
    rcases hπprime.dvd_mul.mp h with h1 | h1
    · exact hπρb h1
    · exact hπρbc h1
  have hπρ₀ : ¬ (1 - hζ.toInteger) ∣ ρ₀ := by
    intro hdvd
    refine hB2 1 h1mem ?_
    rw [← hspanρ₀, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
    exact hdvd
  have hρ₀0 : ρ₀ ≠ 0 := by
    intro h0
    refine hπρ₀ ?_
    rw [h0]
    exact dvd_zero _
  have hKd1 : 1 ≤ 2 * S.m - 2 * p := by
    have h4 : 2 ∣ p - 1 := by
      have hodd := hpri.out.odd_of_ne_two (by omega)
      rw [Nat.odd_iff] at hodd
      omega
    have hub : p * (p - 1) ≤ 2 * S.m := by
      have h6 : 2 ∣ p * (p - 1) := Dvd.dvd.mul_left h4 p
      have h7 := S.hm
      omega
    have h8 : p * 4 ≤ p * (p - 1) := Nat.mul_le_mul_left p (by omega)
    omega
  -- assemble the next situation
  obtain ⟨S', hS'm, hS'ξ⟩ := next_situation S hp hη₁eq hwreal hρ₀real
    hcab hca0 hcb0 hπprodA hπprodB hπρ₀ hρ₀0
  -- the invariant at the next level
  have hℓS'ξ : ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ S'.ξ := by
    rw [hS'ξ, pow_two]
    exact Dvd.dvd.mul_right hℓρ₀ _
  -- the measure data
  refine ⟨S', B 1,
    ∏ ζ' ∈ (nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ))).erase 1, B ζ',
    hℓS'ξ, hS'm, ?_, ?_, ?_, ?_⟩
  · rw [hS'ξ]
    exact hsq0
  · rw [← hBprod]
    exact (Finset.mul_prod_erase _ _ h1mem).symm
  · refine IsCoprime.prod_right ?_
    intro ζ' hζ'mem
    exact hBpair 1 h1mem ζ' (Finset.mem_of_mem_erase hζ'mem)
      (Ne.symm (Finset.ne_of_mem_erase hζ'mem))
  · intro htop
    have hfac_top : ∀ ζ' ∈ (nthRootsFinset p
        (1 : 𝓞 (CyclotomicField p ℚ))).erase 1, B ζ' = ⊤ := by
      intro ζ' hζ'mem
      have h1 : B ζ' ∣ ∏ ζ'' ∈ (nthRootsFinset p
          (1 : 𝓞 (CyclotomicField p ℚ))).erase 1, B ζ'' :=
        Finset.dvd_prod_of_mem _ hζ'mem
      have h2 := Ideal.le_of_dvd h1
      rw [htop] at h2
      exact top_le_iff.mp h2
    have hmem1 : hζ.toInteger ^ 1 ∈ (nthRootsFinset p
        (1 : 𝓞 (CyclotomicField p ℚ))).erase 1 :=
      Finset.mem_erase.mpr ⟨hne10, hmem 1⟩
    have hmemp1 : hζ.toInteger ^ (p - 1) ∈ (nthRootsFinset p
        (1 : 𝓞 (CyclotomicField p ℚ))).erase 1 :=
      Finset.mem_erase.mpr ⟨by
        intro h
        exact hpinj (p - 1) 0 (by omega) (by omega) (by omega)
          (by rw [pow_zero]; exact h), hmem (p - 1)⟩
    have hN : Ideal.span {S.ω + hζ.toInteger ^ 1 * S.θ}
        = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} := by
      have h1 := hBeq 1 (by omega) (by omega)
      rw [hfac_top _ hmem1] at h1
      rwa [Ideal.top_pow, Ideal.mul_top] at h1
    have hD : Ideal.span {S.ω + hζ.toInteger ^ (p - 1) * S.θ}
        = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} := by
      have h1 := hBeq (p - 1) (by omega) (by omega)
      rw [hfac_top _ hmemp1] at h1
      rwa [Ideal.top_pow, Ideal.mul_top] at h1
    have hNE : S.ω + S.θ ≠ 0 := by
      intro h0
      have h1 : Ideal.span ({S.ω + S.θ} : Set (𝓞 (CyclotomicField p ℚ)))
          = (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
        rw [h0, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      rw [hB₀eq] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact h𝔭ne (pow_eq_zero_iff (by omega : 2 * S.m - (p - 1) ≠ 0) |>.mp h2)
      · refine hB2 1 h1mem ?_
        rw [pow_eq_zero_iff hpri.out.ne_zero |>.mp h2]
        exact dvd_zero _
    exact minimal_case_contradiction S hp hvand' hNE hN hD

set_option maxHeartbeats 1000000 in -- heavy elaboration: exceeds the default heartbeat budget
/-- **The measure strictly decreases** along the 9.5 descent, invariant
included. -/
theorem descent_step_meas_95 {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) (hp : 3 < p) (hvand : IsVandiverPrime p)
    (hℓp : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    (hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1)
    (hℓξ : ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ S.ξ) :
    ∃ S' : Situation92 hζ,
      ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ S'.ξ ∧ meas S' < meas S := by
  classical
  obtain ⟨S', B₀, Brest, hℓ', _, hξ', hξ, hcop, hBtop⟩ :=
    descent_step_95 S hp hvand hℓp hμ hℓk hkeven hQall hℓξ
  refine ⟨S', hℓ', ?_⟩
  have hξne : Ideal.span ({S.ξ} : Set (𝓞 (CyclotomicField p ℚ)))
      ≠ (0 : Ideal (𝓞 (CyclotomicField p ℚ))) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact S.hξ0
  have hB₀ne : B₀ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hξ
    exact hξne hξ
  have hBrne : Brest ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hξ
    exact hξne hξ
  have hmeas' : meas S' = (normalizedFactors B₀).toFinset.card := by
    rw [meas, hξ', show (B₀ ^ 2 : Ideal (𝓞 (CyclotomicField p ℚ)))
        = B₀ * B₀ from sq B₀, normalizedFactors_mul hB₀ne hB₀ne]
    simp [Multiset.toFinset_add]
  have hsup : B₀ ⊔ Brest = ⊤ := by
    obtain ⟨a, b, hab⟩ := hcop
    refine top_le_iff.mp ?_
    rw [show (⊤ : Ideal (𝓞 (CyclotomicField p ℚ))) = 1 from Ideal.one_eq_top.symm,
      ← hab, Submodule.add_eq_sup]
    refine sup_le ?_ ?_
    · exact le_trans Ideal.mul_le_left le_sup_left
    · exact le_trans Ideal.mul_le_left le_sup_right
  have hdisj : Disjoint (normalizedFactors B₀).toFinset
      (normalizedFactors Brest).toFinset := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    rw [Multiset.mem_toFinset] at hq1 hq2
    have hqprime : Prime q := prime_of_normalized_factor _ hq1
    have h1 : B₀ ≤ q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hq1)
    have h2 : Brest ≤ q := Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hq2)
    have h3 : (⊤ : Ideal (𝓞 (CyclotomicField p ℚ))) ≤ q := by
      rw [← hsup]
      exact sup_le h1 h2
    refine hqprime.not_unit (Ideal.isUnit_iff.mpr (top_le_iff.mp h3))
  have hBrnonempty : (normalizedFactors Brest).toFinset.Nonempty := by
    obtain ⟨q, hq⟩ := exists_mem_normalizedFactors hBrne (by
      rw [Ideal.isUnit_iff]
      exact hBtop)
    exact ⟨q, Multiset.mem_toFinset.mpr hq⟩
  rw [hmeas', meas, hξ, normalizedFactors_mul hB₀ne hBrne, Multiset.toFinset_add]
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset Finset.subset_union_left]
  obtain ⟨x, hx⟩ := hBrnonempty
  exact ⟨x, Finset.mem_union_right _ hx,
    fun hmem => (Finset.disjoint_left.mp hdisj hmem) hx⟩

/-- **No `ℓ`-marked situation exists**: infinite descent on the measure, with
the invariant carried along. -/
theorem no_situation_95 {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (hp : 3 < p) (hvand : IsVandiverPrime p)
    (hℓp : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    (hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1) :
    ¬ ∃ S : Situation92 hζ, ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ S.ξ := by
  rintro ⟨S, hℓξ⟩
  have hdesc : ∀ n, ∀ S' : Situation92 hζ,
      ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ S'.ξ → meas S' = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S' hℓ' hSn
      obtain ⟨S'', hℓ'', hlt⟩ :=
        descent_step_meas_95 S' hp hvand hℓp hμ hℓk hkeven hQall hℓ'
      exact ih (meas S'') (hSn ▸ hlt) S'' hℓ'' rfl
  exact hdesc (meas S) S hℓξ rfl

/-- **The rational entry with the ℓ-invariant**: a rational Case II solution
with `ℓ ∣ z` (Lemma 9.7's output) seeds a situation with `ℓ ∣ ξ` — the
initial `ξ` is the prime-to-`p` part of `z`, and `ℓ ≠ p` inherits the
divisibility. -/
theorem situation95_of_rational {ζ : CyclotomicField p ℚ}
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p) (hℓnep : ℓ ≠ p)
    {x y z : ℤ} (hxyz : x ^ p + y ^ p = z ^ p)
    (hz0 : z ≠ 0) (hpz : (p : ℤ) ∣ z) (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y)
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (hℓz : (ℓ : ℤ) ∣ z) :
    ∃ S : Situation92 hζ, ((ℓ : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ S.ξ := by
  classical
  obtain ⟨a, w, hzw, hpw⟩ : ∃ (a : ℕ) (w : ℤ), z = p ^ a * w ∧ ¬ (p : ℤ) ∣ w := by
    have hfin : FiniteMultiplicity ((p : ℤ)) z :=
      Int.finiteMultiplicity_iff.mpr ⟨by
        rw [Int.natAbs_natCast]
        exact hpri.out.ne_one, hz0⟩
    obtain ⟨m, hm1, hm2⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    exact ⟨_, m, hm1, hm2⟩
  -- the invariant: ℓ ∣ w
  have hℓint : Prime ((ℓ : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hℓpri.out
  have hℓw : ((ℓ : ℕ) : ℤ) ∣ w := by
    rcases hℓint.dvd_mul.mp (hzw ▸ hℓz) with h1 | h1
    · exfalso
      have h2 : ((ℓ : ℕ) : ℤ) ∣ ((p : ℕ) : ℤ) := hℓint.dvd_of_dvd_pow h1
      have h3 : ℓ ∣ p := Int.natCast_dvd_natCast.mp h2
      exact hℓnep ((Nat.prime_dvd_prime_iff_eq hℓpri.out hpri.out).mp h3)
    · exact h1
  have ha1 : 1 ≤ a := by
    by_contra ha
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero, one_mul] at hzw
    exact hpw (hzw ▸ hpz)
  obtain ⟨uu, huu⟩ := lambda0_pow_associated hζ hp
  have hkey : (lambda0 hζ) ^ (((p - 1) / 2) * (a * p))
      * ((uu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) ^ (a * p)
      = ((p : 𝓞 (CyclotomicField p ℚ))) ^ (a * p) := by
    rw [pow_mul, ← mul_pow, huu]
  have hO : ((x : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p
      + ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p
      = ((uu ^ (a * p) : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (lambda0 hζ) ^ (((p - 1) / 2) * (a * p))
        * ((w : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p := by
    have h1 : ((x : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p
        + ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p
        = ((p : 𝓞 (CyclotomicField p ℚ))) ^ (a * p)
          * ((w : ℤ) : 𝓞 (CyclotomicField p ℚ)) ^ p := by
      have h2 := congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 (CyclotomicField p ℚ))) hxyz
      push_cast at h2
      rw [h2, hzw]
      push_cast
      rw [mul_pow, ← pow_mul]
    rw [h1, ← hkey, Units.val_pow_eq_pow_val]
    ring
  have hlamne : (lambda0 hζ) ^ (((p - 1) / 2) * (a * p)) ≠ 0 :=
    pow_ne_zero _ (lambda0_ne_zero hζ hp)
  have hηreal : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      (((uu ^ (a * p) : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
      = (((uu ^ (a * p) : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hkey
    simp only [map_mul, map_pow, map_natCast, conjO_lambda0 hζ] at h1
    rw [← hkey] at h1
    have h2 := mul_left_cancel₀ hlamne h1
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact h2
  have hcast : ∀ {u v : ℤ}, IsCoprime u v →
      IsCoprime (Ideal.span {((u : ℤ) : 𝓞 (CyclotomicField p ℚ))})
        (Ideal.span {((v : ℤ) : 𝓞 (CyclotomicField p ℚ))}) := by
    intro u v huv
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (huv.map (Int.castRingHom (𝓞 (CyclotomicField p ℚ))))
  have hw_dvd : w ∣ z := ⟨p ^ a, by rw [hzw]; ring⟩
  refine ⟨{
    ω := ((x : ℤ) : 𝓞 (CyclotomicField p ℚ))
    θ := ((y : ℤ) : 𝓞 (CyclotomicField p ℚ))
    ξ := ((w : ℤ) : 𝓞 (CyclotomicField p ℚ))
    η := uu ^ (a * p)
    m := ((p - 1) / 2) * (a * p)
    hm := ?_
    hm_dvd := ⟨2 * ((p - 1) / 2) * a, by ring⟩
    hω_real := conjO_intCast x
    hθ_real := conjO_intCast y
    hξ_real := conjO_intCast w
    hη_real := hηreal
    heq := hO
    hωθ := hcast hxy
    hωξ := hcast (IsCoprime.of_isCoprime_of_dvd_right hxz hw_dvd)
    hθξ := hcast (IsCoprime.of_isCoprime_of_dvd_right hyz hw_dvd)
    hlamω := fun h => hpx ((one_sub_zeta_dvd_intCast_iff hζ x).mp h)
    hlamθ := fun h => hpy ((one_sub_zeta_dvd_intCast_iff hζ y).mp h)
    hlamξ := fun h => hpw ((one_sub_zeta_dvd_intCast_iff hζ w).mp h)
    hξ0 := fun h => by
      have hw0 : w = 0 := by exact_mod_cast h
      exact hz0 (by rw [hzw, hw0, mul_zero]) }, ?_⟩
  · -- the m-invariant
    have hev : 2 ∣ p - 1 := by
      have hodd := hpri.out.odd_of_ne_two (by omega)
      rw [Nat.odd_iff] at hodd
      omega
    have h1 : p * (p - 1) / 2 = p * ((p - 1) / 2) := Nat.mul_div_assoc p hev
    rw [h1, mul_comm p ((p - 1) / 2)]
    exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left p (by omega))
  · -- the ℓ-invariant
    obtain ⟨c, hc⟩ := hℓw
    refine ⟨((c : ℤ) : 𝓞 (CyclotomicField p ℚ)), ?_⟩
    change ((w : ℤ) : 𝓞 (CyclotomicField p ℚ)) = _
    exact_mod_cast hc

/-- **Case II via the 9.5 route**: the single all-even-index `Q_i` certificate
refutes any rational Case II solution
with `ℓ ∣ z` — and `ℓ ∣ z` is exactly Lemma 9.7's output. -/
theorem caseII_95 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 3 < p) (hvand : IsVandiverPrime p)
    (hℓp : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    (hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1)
    {x y z : ℤ} (hxyz : x ^ p + y ^ p = z ^ p)
    (hz0 : z ≠ 0) (hpz : (p : ℤ) ∣ z) (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y)
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (hℓz : (ℓ : ℤ) ∣ z) :
    False := by
  have hℓnep : ℓ ≠ p := by
    intro h
    rw [h, Nat.mod_self] at hℓp
    omega
  exact no_situation_95 hp hvand hℓp hμ hℓk hkeven hQall
    (situation95_of_rational hζ (by omega) hℓnep hxyz hz0 hpz hpx hpy
      hxy hxz hyz hℓz)

end Spine

/-! ### Lemmas 9.6 and 9.7 (merged from CaseII95Factor_scratch.lean) -/

section Factor96


open CyclotomicNT Polynomial NumberField NumberField.IsCMField Ideal FltVandiver
open scoped NumberField
open scoped nonZeroDivisors


section ZModCore

open Finset

variable {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} {ζ : R}

/-- Geometric sum of a nontrivial `n`-th root of unity vanishes. -/
lemma geom_sum_eq_zero_of_pow_eq_one {x : R} {n : ℕ} (hx : x ^ n = 1) (hx1 : x ≠ 1) :
    ∑ i ∈ range n, x ^ i = 0 := by
  have h := geom_sum_mul x n
  rw [hx, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hx1)

/-- `∑_{a<p} ζ^{ca}` is `p` or `0` according to `p ∣ c`. -/
lemma sum_pow_prim (hζ : IsPrimitiveRoot ζ p) (c : ℕ) :
    ∑ a ∈ range p, ζ ^ (c * a) = if p ∣ c then (p : R) else 0 := by
  have hpow : ∀ a ∈ range p, ζ ^ (c * a) = (ζ ^ c) ^ a := fun a _ => by
    rw [← pow_mul]
  rw [Finset.sum_congr rfl hpow]
  split_ifs with h
  · rw [show (ζ ^ c) = 1 from (hζ.pow_eq_one_iff_dvd c).mpr h]
    simp
  · refine geom_sum_eq_zero_of_pow_eq_one ?_ ?_
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    · exact fun h1 => h ((hζ.pow_eq_one_iff_dvd c).mp h1)

/-- Master expansion: `∑_{a<p} ζ^{ca}(y − ζ^a z)^k` collapses to the binomial
terms whose `ζ`-frequency `c + (k−m)` is divisible by `p`. -/
theorem sum_pow_mul_sub_pow (hζ : IsPrimitiveRoot ζ p) (c k : ℕ) (y z : R) :
    ∑ a ∈ range p, ζ ^ (c * a) * (y - ζ ^ a * z) ^ k
      = ∑ m ∈ range (k + 1),
          (if p ∣ c + (k - m) then (p : R) else 0)
            * (y ^ m * (-z) ^ (k - m) * (k.choose m)) := by
  have step : ∀ a ∈ range p,
      ζ ^ (c * a) * (y - ζ ^ a * z) ^ k
        = ∑ m ∈ range (k + 1),
            ζ ^ ((c + (k - m)) * a) * (y ^ m * (-z) ^ (k - m) * (k.choose m)) := by
    intro a _
    rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : (-(ζ ^ a * z)) ^ (k - m) = ζ ^ (a * (k - m)) * (-z) ^ (k - m) := by
      rw [show -(ζ ^ a * z) = ζ ^ a * (-z) by ring, mul_pow, ← pow_mul]
    rw [h1, show (c + (k - m)) * a = c * a + a * (k - m) by ring, pow_add]
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_mul, sum_pow_prim hζ]

/-- Identity A: with weight `ζ^{ca}`, `1 ≤ c` and `c + k < p`, the sum vanishes. -/
theorem sum_A (hζ : IsPrimitiveRoot ζ p) {c k : ℕ} (hc : 0 < c) (hck : c + k < p)
    (y z : R) :
    ∑ a ∈ range p, ζ ^ (c * a) * (y - ζ ^ a * z) ^ k = 0 := by
  rw [sum_pow_mul_sub_pow hζ c k y z]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [if_neg, zero_mul]
  intro hdvd
  have hle : p ≤ c + (k - m) := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Identity B: with weight `ζ^{(p−1)a}` (= `ζ^{−a}`), `1 ≤ k ≤ p − 2`, only the
`m = k − 1` binomial term survives: the sum is `−(p·k·z·y^{k−1})`. -/
theorem sum_B (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 < p)
    (y z : R) :
    ∑ a ∈ range p, ζ ^ ((p - 1) * a) * (y - ζ ^ a * z) ^ k
      = -((p : R) * k * z * y ^ (k - 1)) := by
  rw [sum_pow_mul_sub_pow hζ (p - 1) k y z]
  rw [Finset.sum_eq_single (k - 1)]
  · rw [show p - 1 + (k - (k - 1)) = p by omega, if_pos (dvd_refl p)]
    rw [show k - (k - 1) = 1 by omega]
    have hch : (k.choose (k - 1)) = k := by
      rw [← Nat.choose_symm (Nat.sub_le k 1), Nat.sub_sub_self hk1, Nat.choose_one_right]
    rw [hch, pow_one]
    ring
  · intro m hm hne
    rw [if_neg, zero_mul]
    intro hdvd
    have hle : p ≤ p - 1 + (k - m) := Nat.le_of_dvd (by omega) hdvd
    have hmk' : m < k + 1 := Finset.mem_range.mp hm
    have hlt : p - 1 + (k - m) < 2 * p := by omega
    -- p − 1 + (k − m) ∈ [p, 2p); divisibility forces = p, i.e. m = k − 1: hne.
    have heq : p - 1 + (k - m) = p := by
      obtain ⟨c, hc⟩ := hdvd
      rcases c with _ | _ | c
      · simp at hc
        omega
      · simpa using hc
      · exfalso
        have h2 : p * 2 ≤ p * (c + 1 + 1) := Nat.mul_le_mul_left p (by omega)
        omega
    omega
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **Core of Washington Lemma 9.7**: if `(y − ζ^a z)^k ≡ (y − ζ^{−a} z)^k mod I`
for every `a < p`, then `p·k·z·y^{k−1} ∈ I`. (`ζ^{−a}` is written `ζ^{(p−1)a}`.) -/
theorem lemma_9_7_core (hζ : IsPrimitiveRoot ζ p) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 < p)
    {I : Ideal R} {y z : R}
    (h : ∀ a ∈ range p, (y - ζ ^ a * z) ^ k - (y - ζ ^ ((p - 1) * a) * z) ^ k ∈ I) :
    (p : R) * k * z * y ^ (k - 1) ∈ I := by
  have hp1 : 1 ≤ p := by omega
  have hcop : (p - 1).Coprime p := by
    have h2 : (p - 1).gcd ((p - 1) + 1) = 1 := by
      rw [Nat.gcd_self_add_right, Nat.gcd_one_right]
    simpa [Nat.Coprime, Nat.sub_add_cancel hp1] using h2
  have hζ' : IsPrimitiveRoot (ζ ^ (p - 1)) p := hζ.pow_of_coprime _ hcop
  have hA : ∑ a ∈ range p, (ζ ^ (p - 1)) ^ (1 * a) * (y - (ζ ^ (p - 1)) ^ a * z) ^ k = 0 :=
    sum_A hζ' one_pos (by omega) y z
  have hB := sum_B hζ hk1 hk y z
  have hsplit :
      ∑ a ∈ range p,
          ζ ^ ((p - 1) * a) * ((y - ζ ^ a * z) ^ k - (y - ζ ^ ((p - 1) * a) * z) ^ k)
        = -((p : R) * k * z * y ^ (k - 1)) := by
    have e1 : ∀ a ∈ range p,
        ζ ^ ((p - 1) * a) * ((y - ζ ^ a * z) ^ k - (y - ζ ^ ((p - 1) * a) * z) ^ k)
          = ζ ^ ((p - 1) * a) * (y - ζ ^ a * z) ^ k
            - (ζ ^ (p - 1)) ^ (1 * a) * (y - (ζ ^ (p - 1)) ^ a * z) ^ k := by
      intro a _
      rw [one_mul, ← pow_mul]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, hA, sub_zero, hB]
  have hmem :
      ∑ a ∈ range p,
          ζ ^ ((p - 1) * a) * ((y - ζ ^ a * z) ^ k - (y - ζ ^ ((p - 1) * a) * z) ^ k) ∈ I :=
    Ideal.sum_mem _ fun a ha => I.mul_mem_left _ (h a ha)
  rw [hsplit] at hmem
  simpa using I.neg_mem hmem

/-- **Washington Lemma 9.7, reduction side.** In `ZMod ℓ` with `ℓ = kp + 1`:
if for every `a` the reductions of `y − ζ^a z` and its conjugate partner
`y − ζ^{−a} z` split as (same `g`) times nonzero `p`-th powers — the image of
`y − ζ^a z = γ_a σ_a^p`, `γ_a = γ_{−a}` real under `redHom` — then `z ≡ 0`,
i.e. `ℓ ∣ z` upstairs. The upstream (𝓞K-level) Lemma 9.7 is this plus `redHom`
applied to Lemma 9.6's equations. -/
theorem lemma_9_7_zmod {ℓ : ℕ} [Fact ℓ.Prime] {p k : ℕ} {μ : ZMod ℓ}
    (hμ : IsPrimitiveRoot μ p) (hk1 : 1 ≤ k) (hkp : k + 1 < p) (hℓk : ℓ = k * p + 1)
    {yb zb : ZMod ℓ} (hy : yb ≠ 0)
    (heq : ∀ a ∈ range p, ∃ g s₁ s₂ : ZMod ℓ, s₁ ≠ 0 ∧ s₂ ≠ 0 ∧
      yb - μ ^ a * zb = g * s₁ ^ p ∧ yb - μ ^ ((p - 1) * a) * zb = g * s₂ ^ p) :
    zb = 0 := by
  have hℓ1 : ℓ - 1 = k * p := by omega
  have hcore : ∀ a ∈ range p,
      (yb - μ ^ a * zb) ^ k - (yb - μ ^ ((p - 1) * a) * zb) ^ k
        ∈ (⊥ : Ideal (ZMod ℓ)) := by
    intro a ha
    obtain ⟨g, s₁, s₂, hs₁, hs₂, he₁, he₂⟩ := heq a ha
    have hpow : ∀ s : ZMod ℓ, s ≠ 0 → (s ^ p) ^ k = 1 := by
      intro s hs
      rw [← pow_mul, mul_comm p k, ← hℓ1]
      exact ZMod.pow_card_sub_one_eq_one hs
    rw [he₁, he₂, mul_pow, mul_pow, hpow s₁ hs₁, hpow s₂ hs₂]
    simp
  have hmem := lemma_9_7_core hμ hk1 hkp hcore
  rw [Ideal.mem_bot] at hmem
  have hpk : (p : ZMod ℓ) * (k : ZMod ℓ) ≠ 0 := by
    have h1 : (p : ZMod ℓ) * (k : ZMod ℓ) = ((k * p : ℕ) : ZMod ℓ) := by
      push_cast
      ring
    have h2 : ((k * p : ℕ) : ZMod ℓ) = -1 := by
      rw [← hℓ1, Nat.cast_sub (by omega : 1 ≤ ℓ), ZMod.natCast_self]
      simp
    rw [h1, h2]
    exact neg_ne_zero.mpr one_ne_zero
  rcases mul_eq_zero.mp hmem with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hpk
    · exact h'
  · exact absurd h (pow_ne_zero _ hy)

/-- **Washington Lemma 9.6, reduction-side endgame.** Suppose `ℓ ∣ y` (so the
reduced equations read `−μ^a·z ≡ γ_a·σ_a^p`). Dividing the `a` and `−a`
equations gives `μ^{2a} = (σ_a/σ̄_a)^p`, an element of order `p²` in
`(ZMod ℓ)ˣ` — impossible, since `p² ∤ ℓ − 1 = kp` when `k < p − 1`. -/
theorem lemma_9_6_zmod {ℓ : ℕ} [Fact ℓ.Prime] {p k : ℕ} {μ : ZMod ℓ}
    (hpp : p.Prime)
    (hμ : IsPrimitiveRoot μ p) (hp2 : 2 < p) (hkp : k < p - 1) (hℓk : ℓ = k * p + 1)
    {zb : ZMod ℓ} (hz : zb ≠ 0) {a : ℕ} (ha : ¬ p ∣ a)
    {g s₁ s₂ : ZMod ℓ} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (he₁ : -(μ ^ a * zb) = g * s₁ ^ p)
    (he₂ : -(μ ^ ((p - 1) * a) * zb) = g * s₂ ^ p) : False := by
  have hppos : 0 < p := by omega
  have hμ0 : μ ≠ 0 := fun h0 => by
    have := hμ.pow_eq_one
    rw [h0, zero_pow (by omega : p ≠ 0)] at this
    exact zero_ne_one this
  have hg : g ≠ 0 := by
    intro h0
    rw [h0, zero_mul, neg_eq_zero] at he₁
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hz) he₁
  -- cross-multiplied key: s₁^p · μ^{(p−1)a} = s₂^p · μ^a, then clear μ powers
  have hμp : μ ^ (p * a) = 1 := by
    rw [pow_mul, hμ.pow_eq_one, one_pow]
  have hkey : g * (s₁ ^ p * μ ^ ((p - 1) * a)) = g * (s₂ ^ p * μ ^ a) := by
    have h1 : g * s₁ ^ p * μ ^ ((p - 1) * a) = -(μ ^ a * zb) * μ ^ ((p - 1) * a) := by
      rw [he₁]
    have h2 : g * s₂ ^ p * μ ^ a = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by
      rw [he₂]
    have h3 : -(μ ^ a * zb) * μ ^ ((p - 1) * a) = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by
      ring
    calc g * (s₁ ^ p * μ ^ ((p - 1) * a)) = g * s₁ ^ p * μ ^ ((p - 1) * a) := by ring
      _ = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by rw [h1, h3]
      _ = g * s₂ ^ p * μ ^ a := h2.symm
      _ = g * (s₂ ^ p * μ ^ a) := by ring
  have hkey' : s₁ ^ p * μ ^ ((p - 1) * a) = s₂ ^ p * μ ^ a :=
    mul_left_cancel₀ hg hkey
  -- multiply by μ^a: s₁^p = s₂^p · μ^{2a}
  have hup : s₁ ^ p = s₂ ^ p * μ ^ (2 * a) := by
    have h4 : s₁ ^ p * (μ ^ ((p - 1) * a) * μ ^ a) = s₂ ^ p * (μ ^ a * μ ^ a) := by
      calc s₁ ^ p * (μ ^ ((p - 1) * a) * μ ^ a)
          = (s₁ ^ p * μ ^ ((p - 1) * a)) * μ ^ a := by ring
        _ = (s₂ ^ p * μ ^ a) * μ ^ a := by rw [hkey']
        _ = s₂ ^ p * (μ ^ a * μ ^ a) := by ring
    have h5 : μ ^ ((p - 1) * a) * μ ^ a = 1 := by
      rw [← pow_add, show (p - 1) * a + a = p * a by
        have : 1 ≤ p := by omega
        zify [this]
        ring, hμp]
    have h6 : μ ^ a * μ ^ a = μ ^ (2 * a) := by
      rw [← pow_add, two_mul]
    rw [h5, h6, mul_one] at h4
    exact h4
  -- u := s₁/s₂ has u^p = μ^{2a}, an element of order p
  set u : ZMod ℓ := s₁ * s₂⁻¹ with hu
  have hupow : u ^ p = μ ^ (2 * a) := by
    rw [hu, mul_pow, hup, mul_comm (s₂ ^ p) (μ ^ (2 * a)), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hs₂, one_pow, mul_one]
  have hp2a : ¬ p ∣ 2 * a := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h2 | hA
    · exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
    · exact ha hA
  -- u^p = μ^{2a} ≠ 1, but u^{p²} = 1: u has order p², so p² ∣ ℓ − 1 = kp.
  have hne1 : μ ^ (2 * a) ≠ 1 := fun h1 => hp2a ((hμ.pow_eq_one_iff_dvd _).mp h1)
  have hupp : u ^ (p * p) = 1 := by
    rw [pow_mul, hupow, ← pow_mul, mul_comm (2 * a) p, pow_mul, hμ.pow_eq_one, one_pow]
  have hdvd_pp : orderOf u ∣ p ^ 2 := by
    rw [pow_two]
    exact orderOf_dvd_of_pow_eq_one hupp
  have hnot_p : ¬ orderOf u ∣ p := by
    intro hdp
    exact hne1 (by rw [← hupow]; exact orderOf_dvd_iff_pow_eq_one.mp hdp)
  have hord : orderOf u = p ^ 2 := by
    obtain ⟨m, hm2, hm⟩ := (Nat.dvd_prime_pow hpp).mp hdvd_pp
    interval_cases m
    · rw [pow_zero] at hm
      rw [hm] at hnot_p
      exact absurd (one_dvd p) hnot_p
    · rw [pow_one] at hm
      rw [hm] at hnot_p
      exact absurd dvd_rfl hnot_p
    · exact hm
  have hu0 : u ≠ 0 := mul_ne_zero hs₁ (inv_ne_zero hs₂)
  have hdvd_card : orderOf u ∣ ℓ - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hu0)
  rw [hord] at hdvd_card
  have hpk : p ∣ k := by
    have h7 : p * p ∣ k * p := by
      rw [← pow_two]
      exact hdvd_card.trans (dvd_of_eq (by omega))
    exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < p)).mp h7
  have hk1 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · have h8 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
      simp at hℓk
      omega
    · exact h
  have hplek : p ≤ k := Nat.le_of_dvd hk1 hpk
  omega

end ZModCore


variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]

/-- Pairwise coprimality of the factor ideals `(y − ζ₁ z)`, `(y − ζ₂ z)`. -/
theorem factor_coprime_96 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (_hp : 2 < p) {y z : ℤ} (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z)
    (hyz : IsCoprime y z) :
    ∀ ζ₁ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
    ∀ ζ₂ ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), ζ₁ ≠ ζ₂ →
      IsCoprime
        (Ideal.span {((y : 𝓞 (CyclotomicField p ℚ)) - ζ₁ * (z : 𝓞 (CyclotomicField p ℚ)))})
        (Ideal.span {((y : 𝓞 (CyclotomicField p ℚ)) - ζ₂ * (z : 𝓞 (CyclotomicField p ℚ)))}) := by
  intro ζ₁ h₁ ζ₂ h₂ hne
  set Y : 𝓞 (CyclotomicField p ℚ) := ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) with hY
  set Z : 𝓞 (CyclotomicField p ℚ) := ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) with hZ
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  obtain ⟨𝔮, h𝔮max, h𝔮⟩ := Ideal.exists_le_maximal _ hsup
  have h𝔮prime : 𝔮.IsPrime := h𝔮max.isPrime
  have hf₁ : Y - ζ₁ * Z ∈ 𝔮 :=
    (le_trans le_sup_left h𝔮) (Ideal.mem_span_singleton_self _)
  have hf₂ : Y - ζ₂ * Z ∈ 𝔮 :=
    (le_trans le_sup_right h𝔮) (Ideal.mem_span_singleton_self _)
  -- If `1 − ζ ∈ 𝔮` then `𝔮 = (1−ζ)`, whence `λ ∣ y`, i.e. `p ∣ y` — excluded.
  have hπ𝔮 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ∉ 𝔮 := by
    intro hπ
    have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
      have h1 := hζ.zeta_sub_one_prime'
      rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
          = -(hζ.toInteger - 1) from by ring]
      exact h1.neg
    have h𝔭max : (Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))}).IsMaximal :=
      ((Ideal.span_singleton_prime hπprime.ne_zero).mpr hπprime).isMaximal
        (by simpa [Ne, Ideal.span_singleton_eq_bot] using hπprime.ne_zero)
    have h𝔭le : Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} ≤ 𝔮 :=
      (Ideal.span_singleton_le_iff_mem _).mpr hπ
    have heq : 𝔮 = Ideal.span {(1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))} :=
      (h𝔭max.eq_of_le h𝔮max.ne_top h𝔭le).symm
    have hlamZ : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ∣ Z :=
      (Descent92.one_sub_zeta_dvd_intCast_iff hζ z).mpr hpz
    have hZ𝔮 : Z ∈ 𝔮 := by
      rw [heq]
      exact Ideal.mem_span_singleton.mpr hlamZ
    have hY𝔮 : Y ∈ 𝔮 := by
      have hsplit : Y = (Y - ζ₁ * Z) + ζ₁ * Z := by ring
      rw [hsplit]
      exact add_mem hf₁ (Ideal.mul_mem_left _ _ hZ𝔮)
    have hlamY : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ∣ Y :=
      Ideal.mem_span_singleton.mp (heq ▸ hY𝔮)
    exact hpy ((Descent92.one_sub_zeta_dvd_intCast_iff hζ y).mp hlamY)
  -- root differences are associates of `1 − ζ`, hence not in `𝔮`
  have hdiff𝔮 : (ζ₂ - ζ₁ : 𝓞 (CyclotomicField p ℚ)) ∉ 𝔮 := by
    intro hd
    have hassoc : Associated (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ)) (ζ₂ - ζ₁) :=
      hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        hpri.out (Finset.mem_coe.mpr h₂) (Finset.mem_coe.mpr h₁) hne.symm
    obtain ⟨u, hu⟩ := hassoc
    have h3 : (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ))
        = (ζ₂ - ζ₁) * ((u⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    have h4 : (hζ.toInteger - 1 : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔮 := by
      rw [h3]
      exact Ideal.mul_mem_right _ _ hd
    have h5 : (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔮 := by
      rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
          = -(hζ.toInteger - 1) from by ring]
      exact neg_mem h4
    exact hπ𝔮 h5
  -- so `Z ∈ 𝔮` and `Y ∈ 𝔮`, contradicting `gcd(y, z) = 1`
  have hZ𝔮 : Z ∈ 𝔮 := by
    have hdZ : (ζ₂ - ζ₁) * Z ∈ 𝔮 := by
      have hd : (ζ₂ - ζ₁) * Z = (Y - ζ₁ * Z) - (Y - ζ₂ * Z) := by ring
      rw [hd]
      exact sub_mem hf₁ hf₂
    exact (h𝔮prime.mem_or_mem hdZ).resolve_left hdiff𝔮
  have hY𝔮 : Y ∈ 𝔮 := by
    have hdY : (ζ₂ - ζ₁) * Y ∈ 𝔮 := by
      have hd : (ζ₂ - ζ₁) * Y = ζ₂ * (Y - ζ₁ * Z) - ζ₁ * (Y - ζ₂ * Z) := by ring
      rw [hd]
      exact sub_mem (Ideal.mul_mem_left _ _ hf₁) (Ideal.mul_mem_left _ _ hf₂)
    exact (h𝔮prime.mem_or_mem hdY).resolve_left hdiff𝔮
  obtain ⟨u, v, huv⟩ := hyz
  have hone : (1 : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔮 := by
    have hcast : ((u : ℤ) : 𝓞 (CyclotomicField p ℚ)) * Y
        + ((v : ℤ) : 𝓞 (CyclotomicField p ℚ)) * Z = 1 := by
      rw [hY, hZ]
      exact_mod_cast congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 (CyclotomicField p ℚ))) huv
    rw [← hcast]
    exact add_mem (Ideal.mul_mem_left _ _ hY𝔮) (Ideal.mul_mem_left _ _ hZ𝔮)
  exact h𝔮max.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

/-- **Washington Lemma 9.6, item (a)**: each factor `(y − ζ' z)` is the `p`-th
power of an ideal, and the product of the factor ideals is `(x)^p`. -/
theorem exists_factor_ideals_96 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p)
    (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (hyz : IsCoprime y z) :
    ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      ∃ A : Ideal (𝓞 (CyclotomicField p ℚ)),
        Ideal.span {((y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ)))}
          = A ^ p := by
  set Y : 𝓞 (CyclotomicField p ℚ) := ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) with hY
  set Z : 𝓞 (CyclotomicField p ℚ) := ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) with hZ
  set X : 𝓞 (CyclotomicField p ℚ) := ((x : ℤ) : 𝓞 (CyclotomicField p ℚ)) with hX
  have hodd : Odd p := hpri.out.odd_of_ne_two (by omega)
  have hcast : X ^ p + Y ^ p = Z ^ p := by
    rw [hX, hY, hZ]
    exact_mod_cast congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 (CyclotomicField p ℚ))) hfer
  have hid : Y ^ p + (-Z) ^ p
      = ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), (Y + ζ' * (-Z)) :=
    hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul Y (-Z) hodd
  have hprod_elt : ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), (Y - ζ' * Z)
      = -(X ^ p) := by
    have h1 : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        Y - ζ' * Z = Y + ζ' * (-Z) := fun ζ' _ => by ring
    rw [Finset.prod_congr rfl h1, ← hid, hodd.neg_pow]
    linear_combination hcast
  have hprod_ideal :
      ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)), Ideal.span {(Y - ζ' * Z)}
        = (Ideal.span {X}) ^ p := by
    rw [Ideal.prod_span_singleton, hprod_elt, Ideal.span_singleton_neg,
      Ideal.span_singleton_pow]
  exact Finset.exists_eq_pow_of_mul_eq_pow_of_coprime
    (factor_coprime_96 hζ hp hpy hpz hyz) hprod_ideal

/-! ### Item (b): the pair principality -/

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- Every power of `ζ` is a `p`-th root of unity in `𝓞 K`. -/
theorem zeta_pow_mem_96 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (b : ℕ) :
    hζ.toInteger ^ b ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)) := by
  rw [Polynomial.mem_nthRootsFinset hpri.out.pos, ← pow_mul, mul_comm, pow_mul,
    hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- The factor product: `∏_{ζ'} (y − ζ' z) = −x^p`. -/
theorem prod_factors_96 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) :
    ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        ((y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ)))
      = -(((x : 𝓞 (CyclotomicField p ℚ))) ^ p) := by
  have hodd : Odd p := hpri.out.odd_of_ne_two (by omega)
  have hcast : ((x : 𝓞 (CyclotomicField p ℚ))) ^ p + ((y : 𝓞 (CyclotomicField p ℚ))) ^ p
      = ((z : 𝓞 (CyclotomicField p ℚ))) ^ p := by
    exact_mod_cast congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 (CyclotomicField p ℚ))) hfer
  have hid := hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul
    ((y : 𝓞 (CyclotomicField p ℚ))) (-(z : 𝓞 (CyclotomicField p ℚ))) hodd
  have h1 : ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      (y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ))
        = (y : 𝓞 (CyclotomicField p ℚ)) + ζ' * (-(z : 𝓞 (CyclotomicField p ℚ))) :=
    fun ζ' _ => by ring
  rw [Finset.prod_congr rfl h1, ← hid, hodd.neg_pow]
  linear_combination hcast

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- No factor vanishes (else `x = 0`). -/
theorem factor_ne_zero_96 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0) :
    ∀ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      (y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ)) ≠ 0 := by
  intro ζ' hζ'mem h0
  have h1 : ∏ ζ'' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
      ((y : 𝓞 (CyclotomicField p ℚ)) - ζ'' * (z : 𝓞 (CyclotomicField p ℚ))) = 0 :=
    Finset.prod_eq_zero hζ'mem h0
  rw [prod_factors_96 hζ hp hfer, neg_eq_zero] at h1
  have h2 : ((x : ℤ) : 𝓞 (CyclotomicField p ℚ)) = 0 :=
    pow_eq_zero_iff (by omega : p ≠ 0) |>.mp h1
  exact hx0 (by exact_mod_cast h2)

/-- `λ` divides no factor (`λ ∣ z` but `λ ∤ y`). -/
theorem pi_not_dvd_factor_96 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    {y z : ℤ} (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z)
    (ζ' : 𝓞 (CyclotomicField p ℚ)) :
    ¬ (1 - hζ.toInteger)
      ∣ ((y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ))) := by
  intro hdvd
  have hlamZ : (1 - hζ.toInteger) ∣ ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) :=
    (Descent92.one_sub_zeta_dvd_intCast_iff hζ z).mpr hpz
  have hlamY : (1 - hζ.toInteger) ∣ ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 : ((y : ℤ) : 𝓞 (CyclotomicField p ℚ))
        = (((y : ℤ) : 𝓞 (CyclotomicField p ℚ))
            - ζ' * ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)))
          + ζ' * ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) := by ring
    rw [h1]
    exact dvd_add hdvd (hlamZ.mul_left ζ')
  exact hpy ((Descent92.one_sub_zeta_dvd_intCast_iff hζ y).mp hlamY)

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- Conjugation of a factor: `conj (y − ζ^b z) = y − ζ^{b(p−1)} z`. -/
theorem conj_factor_96 [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) {y z : ℤ} (b : ℕ) :
    (ringOfIntegersComplexConj (CyclotomicField p ℚ)
        : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ))
      ((y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ b * (z : 𝓞 (CyclotomicField p ℚ)))
      = (y : 𝓞 (CyclotomicField p ℚ))
        - hζ.toInteger ^ (b * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)) := by
  set c : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ) :=
    (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) with hc
  have hcζ : c hζ.toInteger = hζ.toInteger ^ (p - 1) := Descent92.conjO_toInteger hζ
  have hcy : c ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) :=
    Descent92.conjO_intCast y
  have hcz : c ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) :=
    Descent92.conjO_intCast z
  rw [map_sub, map_mul, map_pow, hcζ, hcy, hcz, ← pow_mul, mul_comm (p - 1) b]

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- Conjugation swaps the factor ideals: `conj(A_b) = A_{b(p−1)}`. -/
theorem factor_ideal_conjSwap_96 [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) {y z : ℤ} {b : ℕ}
    {A₁ A₂ : Ideal (𝓞 (CyclotomicField p ℚ))}
    (hA₁ : Ideal.span {((y : 𝓞 (CyclotomicField p ℚ))
        - hζ.toInteger ^ b * (z : 𝓞 (CyclotomicField p ℚ)))} = A₁ ^ p)
    (hA₂ : Ideal.span {((y : 𝓞 (CyclotomicField p ℚ))
        - hζ.toInteger ^ (b * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)))} = A₂ ^ p) :
    A₁.map (ringOfIntegersComplexConj (CyclotomicField p ℚ)
        : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) = A₂ := by
  set c : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ) :=
    (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) with hc
  have h1 := congrArg (Ideal.map c) hA₁
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h1
  rw [show c ((y : 𝓞 (CyclotomicField p ℚ))
      - hζ.toInteger ^ b * (z : 𝓞 (CyclotomicField p ℚ)))
      = (y : 𝓞 (CyclotomicField p ℚ))
        - hζ.toInteger ^ (b * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)) from
    conj_factor_96 hζ b] at h1
  rw [hA₂] at h1
  exact pow_left_injective hpri.out.ne_zero h1.symm

/-- **Washington Lemma 9.6, item (b)** — the pair principality: under Vandiver,
`(y − ζ^a z)(y − ζ^{−a} z) = ε′ · ρ′^p` with `ε′` a real unit and `ρ′` real.
Mirror of `step1_real_decomposition`, simpler (no `λ`-power to strip). -/
theorem pair_real_principal_96 [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) (hvand : IsVandiverPrime p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (hyz : IsCoprime y z) (a : ℕ) :
    ∃ (ε' : (𝓞 (CyclotomicField p ℚ))ˣ) (ρ' : 𝓞 (CyclotomicField p ℚ)),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      ∧ ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ' = ρ'
      ∧ ((y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)))
          * ((y : 𝓞 (CyclotomicField p ℚ))
              - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)))
        = ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * ρ' ^ p := by
  classical
  set c : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ) :=
    (ringOfIntegersComplexConj (CyclotomicField p ℚ)
      : 𝓞 (CyclotomicField p ℚ) →+* 𝓞 (CyclotomicField p ℚ)) with hc
  set N₁ : 𝓞 (CyclotomicField p ℚ) :=
    (y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)) with hN₁
  set N₂ : 𝓞 (CyclotomicField p ℚ) :=
    (y : 𝓞 (CyclotomicField p ℚ))
      - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)) with hN₂
  -- the two factor ideals
  obtain ⟨A₁, hA₁⟩ := exists_factor_ideals_96 hζ hp hfer hpy hpz hyz
    (hζ.toInteger ^ a) (zeta_pow_mem_96 hζ a)
  obtain ⟨A₂, hA₂⟩ := exists_factor_ideals_96 hζ hp hfer hpy hpz hyz
    (hζ.toInteger ^ (a * (p - 1))) (zeta_pow_mem_96 hζ (a * (p - 1)))
  -- exponent reduction for the double conjugate
  have hred : (a * (p - 1) * (p - 1)) % p = a % p := by
    have h2 := hpri.out.two_le
    have h3 : a * (p - 1) * (p - 1) = a * ((p - 1) * (p - 1)) := by ring
    have h4 : (p - 1) * (p - 1) = p * (p - 2) + 1 := by
      zify [show 1 ≤ p from by omega, show 2 ≤ p from h2]
      ring
    rw [h3, h4, show a * (p * (p - 2) + 1) = a + (a * (p - 2)) * p from by ring,
      Nat.add_mul_mod_self_right]
  have hA₁' : Ideal.span {((y : 𝓞 (CyclotomicField p ℚ))
      - hζ.toInteger ^ (a * (p - 1) * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)))}
      = A₁ ^ p := by
    rw [Descent92.toInteger_pow_eq_of_mod hζ hred]
    exact hA₁
  -- conjugation swaps the pair
  have hswap1 : A₁.map c = A₂ := factor_ideal_conjSwap_96 hζ hA₁ hA₂
  have hswap2 : A₂.map c = A₁ := factor_ideal_conjSwap_96 hζ hA₂ hA₁'
  set P : Ideal (𝓞 (CyclotomicField p ℚ)) := A₁ * A₂ with hP
  have hfix : P.map c = P := by
    rw [hP, Ideal.map_mul, hswap1, hswap2, mul_comm]
  -- P is coprime to p
  have hπprime : Prime (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ)) := by
    have h1 := hζ.zeta_sub_one_prime'
    rw [show (1 - hζ.toInteger : 𝓞 (CyclotomicField p ℚ))
        = -(hζ.toInteger - 1) from by ring]
    exact h1.neg
  set 𝔭 : Ideal (𝓞 (CyclotomicField p ℚ)) := Ideal.span {(1 - hζ.toInteger)} with h𝔭
  have h𝔭prime : Prime 𝔭 :=
    Ideal.prime_of_isPrime (by
      simpa [h𝔭, Ideal.span_singleton_eq_bot] using hπprime.ne_zero)
      ((Ideal.span_singleton_prime hπprime.ne_zero).mpr hπprime)
  have h𝔭P : ¬ 𝔭 ∣ P := by
    intro hdvd
    have hcases := h𝔭prime.2.2 A₁ A₂ hdvd
    have hkill : ∀ (A : Ideal (𝓞 (CyclotomicField p ℚ)))
        (N : 𝓞 (CyclotomicField p ℚ)), Ideal.span {N} = A ^ p
        → ¬ (1 - hζ.toInteger) ∣ N → ¬ 𝔭 ∣ A := by
      intro A N hspan hnd hdvdA
      have h1 : 𝔭 ∣ A ^ p := hdvdA.trans (dvd_pow_self A hpri.out.ne_zero)
      rw [← hspan] at h1
      exact hnd (Ideal.mem_span_singleton.mp (Ideal.dvd_span_singleton.mp h1))
    rcases hcases with h | h
    · exact hkill A₁ N₁ hA₁ (pi_not_dvd_factor_96 hζ hpy hpz _) h
    · exact hkill A₂ N₂ hA₂ (pi_not_dvd_factor_96 hζ hpy hpz _) h
  have hcop : IsCoprime P (Ideal.span {((p : ℕ) : 𝓞 (CyclotomicField p ℚ))}) :=
    Descent92.deep_ideal_coprime_p hp h𝔭P
  -- P is extended from the real subfield
  obtain ⟨A, hA⟩ := isExtended_of_conjFixed_of_coprime hp hfix (by
    convert hcop using 2)
  -- the pair product, real and generating P^p
  set W : 𝓞 (CyclotomicField p ℚ) := N₁ * N₂ with hW
  have hWspan : Ideal.span {W} = P ^ p := by
    rw [hW, ← Ideal.span_singleton_mul_span_singleton, hA₁, hA₂, hP, mul_pow]
  have hWreal : c W = W := by
    rw [hW, map_mul]
    have h1 : c N₁ = N₂ := conj_factor_96 hζ a
    have h2 : c N₂ = N₁ := by
      have h3 := conj_factor_96 (y := y) (z := z) hζ (a * (p - 1))
      rwa [Descent92.toInteger_pow_eq_of_mod hζ hred] at h3
    rw [h1, h2, mul_comm]
  have hW0 : W ≠ 0 :=
    mul_ne_zero
      (factor_ne_zero_96 hζ hp hfer hx0 _ (zeta_pow_mem_96 hζ a))
      (factor_ne_zero_96 hζ hp hfer hx0 _ (zeta_pow_mem_96 hζ (a * (p - 1))))
  -- W comes from downstairs
  have hW_range : W ∈ Set.range (algebraMap (𝓞 (MaximalRealCyclotomic p))
      (𝓞 (CyclotomicField p ℚ))) := by
    rw [← NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff]
    exact hWreal
  obtain ⟨Wplus, hWplus⟩ := hW_range
  have hApmap : (A ^ p).map (algebraMap (𝓞 (MaximalRealCyclotomic p))
        (𝓞 (CyclotomicField p ℚ)))
      = (Ideal.span {Wplus}).map (algebraMap (𝓞 (MaximalRealCyclotomic p))
        (𝓞 (CyclotomicField p ℚ))) := by
    rw [Ideal.map_pow, ← hA, ← hWspan, Ideal.map_span, Set.image_singleton, hWplus]
  haveI hff : Module.FaithfullyFlat (𝓞 (MaximalRealCyclotomic p))
      (𝓞 (CyclotomicField p ℚ)) := inferInstance
  have hAp : A ^ p = Ideal.span {Wplus} := by
    have h2 := congrArg (Ideal.comap (algebraMap (𝓞 (MaximalRealCyclotomic p))
      (𝓞 (CyclotomicField p ℚ)))) hApmap
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat,
      Ideal.comap_map_eq_self_of_faithfullyFlat] at h2
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, Ideal.zero_eq_bot, Ideal.map_bot] at hA
    apply hW0
    have h1 : Ideal.span {W} = ⊥ := by
      rw [hWspan, hA, ← Ideal.zero_eq_bot, zero_pow (by omega : p ≠ 0)]
    rwa [Ideal.span_singleton_eq_bot] at h1
  -- Vandiver kills the class of A
  have hAmem : A ∈ (Ideal (𝓞 (MaximalRealCyclotomic p)))⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hA0
  have hApmem : A ^ p ∈ (Ideal (𝓞 (MaximalRealCyclotomic p)))⁰ := pow_mem hAmem p
  have hclass : ClassGroup.mk0 ⟨A, hAmem⟩ ^ p = 1 := by
    have hsub : (⟨A, hAmem⟩ : (Ideal (𝓞 (MaximalRealCyclotomic p)))⁰) ^ p
        = ⟨A ^ p, hApmem⟩ := Subtype.ext (by push_cast; ring)
    rw [← map_pow, hsub]
    refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
    rw [hAp]
    exact ⟨⟨Wplus, rfl⟩⟩
  have hA1 := hvand.pow_eq_one_eq_one hclass
  obtain ⟨ρ0plus, hρ0plus⟩ := (ClassGroup.mk0_eq_one_iff hAmem).mp hA1
  set ρ₀ : 𝓞 (CyclotomicField p ℚ) :=
    algebraMap (𝓞 (MaximalRealCyclotomic p)) (𝓞 (CyclotomicField p ℚ)) ρ0plus with hρ₀
  have hPspan : P = Ideal.span {ρ₀} := by
    rw [hA, hρ0plus, Ideal.map_span, Set.image_singleton]
  have hρ₀real : ringOfIntegersComplexConj (CyclotomicField p ℚ) ρ₀ = ρ₀ := by
    rw [NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff]
    exact ⟨ρ0plus, rfl⟩
  -- the unit between W and ρ₀^p
  have hassoc : Associated (ρ₀ ^ p) W := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← Ideal.span_singleton_pow,
      ← hPspan, ← hWspan]
  obtain ⟨u, hu⟩ := hassoc
  have hρ₀ne : ρ₀ ^ p ≠ 0 := by
    intro h0
    exact hW0 (by rw [← hu, h0, zero_mul])
  refine ⟨u, ρ₀, ?_, hρ₀real, ?_⟩
  · have h5 := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) hu
    rw [map_mul, map_pow, hρ₀real] at h5
    rw [show (ringOfIntegersComplexConj (CyclotomicField p ℚ)) W = W from hWreal] at h5
    rw [← hu] at h5
    exact mul_left_cancel₀ hρ₀ne h5
  · rw [← hu]
    ring

/-- **Washington Lemma 9.6, item (d)** — the `(p+1)/2` split: given the pair
principality (item (b)) and the α-ratio being a `p`-th power (item (c), taken
here as a hypothesis), each factor splits as `y − ζ^a z = γ_a·σ_a^p` with `γ_a`
a real unit — and conjugating gives the `−a` partner with the SAME `γ_a`, which
is exactly the pairing Lemma 9.7 consumes. -/
theorem factor_split_96 [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) (hvand : IsVandiverPrime p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (hyz : IsCoprime y z) (a : ℕ)
    (hα : ∃ w : CyclotomicField p ℚ, w ^ p
      = algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          ((y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)))
        / algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          ((y : 𝓞 (CyclotomicField p ℚ))
            - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)))) :
    ∃ (γ : (𝓞 (CyclotomicField p ℚ))ˣ) (σ : 𝓞 (CyclotomicField p ℚ)),
      ringOfIntegersComplexConj (CyclotomicField p ℚ)
        ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      ∧ (y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ))
          = ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * σ ^ p
      ∧ (y : 𝓞 (CyclotomicField p ℚ))
            - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ))
          = ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ) ^ p := by
  classical
  obtain ⟨ε', ρ', hε'real, hρ'real, hpair⟩ :=
    pair_real_principal_96 hζ hp hvand hfer hx0 hpy hpz hyz a
  obtain ⟨w, hw⟩ := hα
  set N₁ : 𝓞 (CyclotomicField p ℚ) :=
    (y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)) with hN₁
  set N₂ : 𝓞 (CyclotomicField p ℚ) :=
    (y : 𝓞 (CyclotomicField p ℚ))
      - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)) with hN₂
  set f : 𝓞 (CyclotomicField p ℚ) →+* CyclotomicField p ℚ :=
    (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)) with hf
  have hfinj : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  have hN₁0 : N₁ ≠ 0 := factor_ne_zero_96 hζ hp hfer hx0 _ (zeta_pow_mem_96 hζ a)
  have hN₂0 : N₂ ≠ 0 := factor_ne_zero_96 hζ hp hfer hx0 _ (zeta_pow_mem_96 hζ (a * (p - 1)))
  have hF0 : f N₁ ≠ 0 := fun h0 => hN₁0 (hfinj (by rw [h0, map_zero]))
  have hB0 : f N₂ ≠ 0 := fun h0 => hN₂0 (hfinj (by rw [h0, map_zero]))
  -- the K-level square identity: (f N₁)² = f ε′ · (f ρ′ · w)^p
  have hsq : (f N₁) ^ 2
      = f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (f ρ' * w) ^ p := by
    have hwB : w ^ p * f N₂ = f N₁ := by
      rw [hw]
      field_simp
    have h1 : (f N₁) ^ 2 * f N₂
        = (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * (f ρ' * w) ^ p) * f N₂ := by
      have hpairK := congrArg f hpair
      rw [map_mul, map_mul, map_pow] at hpairK
      calc (f N₁) ^ 2 * f N₂ = f N₁ * (f N₁ * f N₂) := by ring
        _ = f N₁ * (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * f ρ' ^ p) := by rw [← hpairK]
        _ = (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * f ρ' ^ p) * (w ^ p * f N₂) := by rw [hwB]; ring
        _ = (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              * (f ρ' * w) ^ p) * f N₂ := by ring
    exact mul_right_cancel₀ hB0 h1
  -- (p+1)/2-extraction
  have hodd : Odd p := hpri.out.odd_of_ne_two (by omega)
  have hext := Descent92.half_power_extraction hodd hF0 hsq
  set σhat : CyclotomicField p ℚ := (f ρ' * w) ^ ((p + 1) / 2) / f N₁ with hσhatdef
  have huu : f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      * f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hσp : σhat ^ p = f (N₁ * (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ))
      : 𝓞 (CyclotomicField p ℚ)) ^ ((p + 1) / 2)) := by
    rw [map_mul, map_pow]
    have h2 : f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
          ^ ((p + 1) / 2) * f N₁
        = f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
          ^ ((p + 1) / 2)
          * (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              ^ ((p + 1) / 2) * σhat ^ p) := by
      rw [← hext]
    rw [show f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ))
          ^ ((p + 1) / 2)
          * (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
              ^ ((p + 1) / 2) * σhat ^ p)
        = (f ((ε' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
            * f (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ)) : 𝓞 (CyclotomicField p ℚ)))
            ^ ((p + 1) / 2) * σhat ^ p from by ring, huu, one_pow, one_mul] at h2
    rw [← h2]
    ring
  -- integrality lift
  obtain ⟨σ, hσ⟩ : ∃ σ : 𝓞 (CyclotomicField p ℚ), f σ = σhat := by
    have h1 : IsIntegral ℤ (σhat ^ p) := by
      rw [hσp]
      exact (N₁ * (((ε'⁻¹ : (𝓞 (CyclotomicField p ℚ))ˣ))
        : 𝓞 (CyclotomicField p ℚ)) ^ ((p + 1) / 2)).2
    have h2 : IsIntegral ℤ σhat := h1.of_pow (by omega)
    exact ⟨⟨σhat, h2⟩, rfl⟩
  -- the 𝓞-level split at index a
  set γ : (𝓞 (CyclotomicField p ℚ))ˣ := ε' ^ ((p + 1) / 2) with hγ
  have hγreal : ringOfIntegersComplexConj (CyclotomicField p ℚ)
      ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
      = ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) := by
    rw [hγ, Units.val_pow_eq_pow_val, map_pow, hε'real]
  have heq₁ : N₁ = ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * σ ^ p := by
    apply hfinj
    rw [map_mul, map_pow, hσ, hγ, Units.val_pow_eq_pow_val, map_pow]
    exact hext
  refine ⟨γ, σ, hγreal, heq₁, ?_⟩
  -- conjugate: N₂ = γ · (conj σ)^p
  have hconj := congrArg (ringOfIntegersComplexConj (CyclotomicField p ℚ)) heq₁
  rw [map_mul, map_pow, hγreal] at hconj
  rw [show (ringOfIntegersComplexConj (CyclotomicField p ℚ)) N₁ = N₂ from
    conj_factor_96 hζ a] at hconj
  exact hconj

/-! ### Item (c′): the wild multiplier for `α = (y − ζ^a z)/(y − ζ^{−a} z)` -/

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- `(1 − ζ)^{p−1}` divides `p` (from `lambda0_pow_associated`). -/
theorem one_sub_zeta_pow_dvd_p_96 {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hp : 2 < p) :
    (1 - hζ.toInteger) ^ (p - 1) ∣ ((p : ℕ) : 𝓞 (CyclotomicField p ℚ)) := by
  obtain ⟨uu, huu⟩ := Descent92.lambda0_pow_associated hζ hp
  have hodd := hpri.out.odd_of_ne_two (by omega)
  have heven : 2 * ((p - 1) / 2) = p - 1 := by
    rw [Nat.odd_iff] at hodd
    omega
  have h1 : (Descent92.lambda0 hζ) ^ ((p - 1) / 2)
      = (-hζ.toInteger ^ (p - 1)) ^ ((p - 1) / 2) * (1 - hζ.toInteger) ^ (p - 1) := by
    rw [Descent92.lambda0_eq_unit_mul_sq hζ hp, mul_pow, ← pow_mul, heven]
  refine ⟨(-hζ.toInteger ^ (p - 1)) ^ ((p - 1) / 2)
    * ((uu : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)), ?_⟩
  rw [← huu, h1]
  ring

/-- Freshman's dream with margin: if `d ∣ u − v` and `d^{p−1} ∣ p`, then
`d^p ∣ u^p − v^p`. -/
theorem freshman_96 {R : Type*} [CommRing R] {p : ℕ} (hpp : p.Prime)
    {d u v : R} (hd : d ∣ u - v) (hdp : d ^ (p - 1) ∣ (p : R)) :
    d ^ p ∣ u ^ p - v ^ p := by
  obtain ⟨t, ht⟩ := hd
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hpp v (d * t)
  have hu : u = v + d * t := by linear_combination ht
  obtain ⟨s, hs⟩ := hdp
  have hpow : d ^ (p - 1) * d = d ^ p := by
    rw [← pow_succ]
    congr 1
    have := hpp.two_le
    omega
  have key : u ^ p - v ^ p = d ^ p * t ^ p + d ^ p * (s * v * t * r) := by
    calc u ^ p - v ^ p = (v + d * t) ^ p - v ^ p := by rw [← hu]
      _ = (d * t) ^ p + (p : R) * v * (d * t) * r := by rw [hr]; ring
      _ = d ^ p * t ^ p + (d ^ (p - 1) * s) * v * (d * t) * r := by
          rw [← hs, mul_pow]
      _ = d ^ p * t ^ p + (d ^ (p - 1) * d) * (s * v * t * r) := by ring
      _ = d ^ p * t ^ p + d ^ p * (s * v * t * r) := by rw [hpow]
  rw [key]
  exact dvd_add (Dvd.intro _ rfl) (Dvd.intro _ rfl)

/-- Euler mod `p²`: for `p ∤ y`, `p² ∣ y^{p(p−1)} − 1`. -/
theorem euler_sq_96 {p : ℕ} (hpp : p.Prime) (hp : 2 < p) {y : ℤ}
    (hpy : ¬ (p : ℤ) ∣ y) :
    ((p : ℤ)) ^ 2 ∣ y ^ (p * (p - 1)) - 1 := by
  set w : ℕ := y.natAbs with hw
  have hw0 : w ≠ 0 := by
    intro h0
    exact hpy (by rw [Int.natAbs_eq_zero.mp h0]; exact dvd_zero _)
  have hpw : ¬ p ∣ w := by
    intro hd
    apply hpy
    have h1 : ((p : ℤ)).natAbs ∣ y.natAbs := by simpa using hd
    exact Int.natAbs_dvd_natAbs.mp h1
  have hcop : w.Coprime (p ^ 2) :=
    (Nat.coprime_comm.mp ((hpp.coprime_iff_not_dvd).mpr hpw)).pow_right 2
  have htot : Nat.totient (p ^ 2) = p * (p - 1) := by
    rw [Nat.totient_prime_pow hpp (by omega : 0 < 2)]
    ring_nf
  have hmod : w ^ (p * (p - 1)) ≡ 1 [MOD p ^ 2] := by
    rw [← htot]
    exact Nat.ModEq.pow_totient hcop
  have h1le : 1 ≤ w ^ (p * (p - 1)) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hw0)
  have hdvdN : p ^ 2 ∣ w ^ (p * (p - 1)) - 1 := (Nat.modEq_iff_dvd' h1le).mp hmod.symm
  have hqeven : Even (p * (p - 1)) := by
    have hodd := hpp.odd_of_ne_two (by omega)
    have h2 : Even (p - 1) := Nat.Odd.sub_odd hodd odd_one
    exact h2.mul_left p
  have hyq : y ^ (p * (p - 1)) = ((w : ℤ)) ^ (p * (p - 1)) := by
    rcases Int.natAbs_eq y with h | h
    · rw [h]
    · rw [h]
      exact hqeven.neg_pow _
  have hcast : ((p : ℤ)) ^ 2 ∣ ((w : ℤ)) ^ (p * (p - 1)) - 1 := by
    have h2 : (((w ^ (p * (p - 1)) - 1 : ℕ)) : ℤ)
        = ((w : ℤ)) ^ (p * (p - 1)) - 1 := by
      push_cast [Nat.cast_sub h1le]
      ring
    have h3 := Int.natCast_dvd_natCast.mpr hdvdN
    rw [h2] at h3
    exact_mod_cast h3
  rwa [hyq]

omit [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- **Washington Lemma 9.6, item (c′)** — the wild multiplier: with
`c := (y − ζ^{−a} z)^{p−1}` and `a′ := N₁·N₂^{p(p−1)−1}`, one has
`a′ = α·c^p` and `(ζ − 1)^p ∣ a′ − 1`. Feeds
`isUnramified_adjoinRoot_of_pthRoot_data`. -/
theorem wild_multiplier_96 [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (a : ℕ) :
    ∃ c : CyclotomicField p ℚ, c ≠ 0 ∧ ∃ a' : 𝓞 (CyclotomicField p ℚ),
      algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) a'
        = (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
            ((y : 𝓞 (CyclotomicField p ℚ))
              - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)))
          / algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
            ((y : 𝓞 (CyclotomicField p ℚ))
              - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)))) * c ^ p
      ∧ (hζ.unit' - 1 : 𝓞 (CyclotomicField p ℚ)) ^ p ∣ a' - 1 := by
  classical
  set N₁ : 𝓞 (CyclotomicField p ℚ) :=
    (y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)) with hN₁
  set N₂ : 𝓞 (CyclotomicField p ℚ) :=
    (y : 𝓞 (CyclotomicField p ℚ))
      - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)) with hN₂
  set Y : 𝓞 (CyclotomicField p ℚ) := ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) with hY
  set Z : 𝓞 (CyclotomicField p ℚ) := ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) with hZ
  set d : 𝓞 (CyclotomicField p ℚ) := 1 - hζ.toInteger with hd
  set q : ℕ := p * (p - 1) with hq
  have hq1 : 1 ≤ q := by
    have := hpri.out.two_le
    have h1 : 1 ≤ p - 1 := by omega
    calc 1 = 1 * 1 := by ring
      _ ≤ p * (p - 1) := Nat.mul_le_mul (by omega) h1
  -- λ-divisibilities
  have hd_p : d ^ (p - 1) ∣ ((p : ℕ) : 𝓞 (CyclotomicField p ℚ)) :=
    one_sub_zeta_pow_dvd_p_96 hζ hp
  have hpZ : ((p : ℕ) : 𝓞 (CyclotomicField p ℚ)) ∣ Z := by
    have h1 : (((p : ℤ)) : 𝓞 (CyclotomicField p ℚ)) ∣ (((z : ℤ)) : 𝓞 (CyclotomicField p ℚ)) :=
      map_dvd (Int.castRingHom _) hpz
    rw [show (((p : ℤ)) : 𝓞 (CyclotomicField p ℚ))
      = ((p : ℕ) : 𝓞 (CyclotomicField p ℚ)) from by push_cast; ring, ← hZ] at h1
    exact h1
  have hd1Z : d ^ (p - 1) ∣ Z := hd_p.trans hpZ
  have hdZ : d ∣ Z := (dvd_pow_self d (by omega : p - 1 ≠ 0)).trans hd1Z
  -- d divides differences of ζ-powers
  have hdzeta : ∀ k : ℕ, d ∣ hζ.toInteger ^ k - 1 := by
    intro k
    have h1 : hζ.toInteger - 1 ∣ hζ.toInteger ^ k - 1 := by
      have h2 := sub_dvd_pow_sub_pow hζ.toInteger 1 k
      rwa [one_pow] at h2
    rw [hd, show (1 - hζ.toInteger) = -(hζ.toInteger - 1) from by ring]
    exact (neg_dvd).mpr h1
  have hdiff : d ∣ hζ.toInteger ^ (a * (p - 1)) - hζ.toInteger ^ a := by
    have h1 : hζ.toInteger ^ (a * (p - 1)) - hζ.toInteger ^ a
        = (hζ.toInteger ^ (a * (p - 1)) - 1) - (hζ.toInteger ^ a - 1) := by ring
    rw [h1]
    exact dvd_sub (hdzeta _) (hdzeta _)
  have hdppow : d ^ p = d * d ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    have := hpri.out.two_le
    omega
  -- T1: d^p ∣ N₁ − N₂
  have hT1 : d ^ p ∣ N₁ - N₂ := by
    have h1 : N₁ - N₂ = (hζ.toInteger ^ (a * (p - 1)) - hζ.toInteger ^ a) * Z := by
      rw [hN₁, hN₂]
      ring
    rw [h1, hdppow]
    exact mul_dvd_mul hdiff hd1Z
  -- T2: d^p ∣ N₂^q − 1
  have hT2 : d ^ p ∣ N₂ ^ q - 1 := by
    have hN₂Y : d ∣ N₂ - Y := by
      have h1 : N₂ - Y = -(hζ.toInteger ^ (a * (p - 1)) * Z) := by
        rw [hN₂, hY]
        ring
      rw [h1]
      exact (dvd_neg).mpr ((hdZ).mul_left _)
    have hfresh : d ^ p ∣ N₂ ^ p - Y ^ p := freshman_96 hpri.out hN₂Y hd_p
    have hchain : d ^ p ∣ N₂ ^ q - Y ^ q := by
      have h1 : N₂ ^ q - Y ^ q = (N₂ ^ p) ^ (p - 1) - (Y ^ p) ^ (p - 1) := by
        rw [← pow_mul, ← pow_mul, hq]
      rw [h1]
      exact hfresh.trans (sub_dvd_pow_sub_pow _ _ _)
    have heuler : d ^ p ∣ Y ^ q - 1 := by
      have h1 : ((p : ℤ)) ^ 2 ∣ y ^ q - 1 := euler_sq_96 hpri.out hp hpy
      have h3 : ((((p : ℤ) ^ 2 : ℤ)) : 𝓞 (CyclotomicField p ℚ))
          ∣ (((y ^ q - 1 : ℤ)) : 𝓞 (CyclotomicField p ℚ)) :=
        map_dvd (Int.castRingHom _) h1
      have h2 : ((p : ℕ) : 𝓞 (CyclotomicField p ℚ)) ^ 2 ∣ Y ^ q - 1 := by
        have e1 : ((((p : ℤ) ^ 2 : ℤ)) : 𝓞 (CyclotomicField p ℚ))
            = ((p : ℕ) : 𝓞 (CyclotomicField p ℚ)) ^ 2 := by push_cast; ring
        have e2 : (((y ^ q - 1 : ℤ)) : 𝓞 (CyclotomicField p ℚ)) = Y ^ q - 1 := by
          rw [hY]
          push_cast
          ring
        rwa [e1, e2] at h3
      have h4 : d ^ ((p - 1) * 2) ∣ ((p : ℕ) : 𝓞 (CyclotomicField p ℚ)) ^ 2 := by
        have h5 : (d ^ (p - 1)) ^ 2 ∣ (((p : ℕ)) : 𝓞 (CyclotomicField p ℚ)) ^ 2 :=
          pow_dvd_pow_of_dvd hd_p 2
        rwa [← pow_mul] at h5
      have h6 : d ^ p ∣ d ^ ((p - 1) * 2) := pow_dvd_pow d (by omega)
      exact (h6.trans h4).trans h2
    have hsplit : N₂ ^ q - 1 = (N₂ ^ q - Y ^ q) + (Y ^ q - 1) := by ring
    rw [hsplit]
    exact dvd_add hchain heuler
  -- assemble a′
  set a' : 𝓞 (CyclotomicField p ℚ) := N₁ * N₂ ^ (q - 1) with ha'
  have hsplit' : a' - 1 = (N₁ - N₂) * N₂ ^ (q - 1) + (N₂ ^ q - 1) := by
    have h1 : N₂ ^ q = N₂ ^ (q - 1) * N₂ := by
      rw [← pow_succ]
      congr 1
      omega
    rw [ha', h1]
    ring
  have hdvd : d ^ p ∣ a' - 1 := by
    rw [hsplit']
    exact dvd_add (hT1.mul_right _) hT2
  -- convert to the (ζ − 1)^p form
  have hconv : (hζ.unit' - 1 : 𝓞 (CyclotomicField p ℚ)) ^ p ∣ a' - 1 := by
    have hcoe : ((hζ.unit' : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        = hζ.toInteger := rfl
    have hodd : Odd p := hpri.out.odd_of_ne_two (by omega)
    have h1 : (hζ.unit' - 1 : 𝓞 (CyclotomicField p ℚ)) ^ p = -(d ^ p) := by
      rw [show (hζ.unit' - 1 : 𝓞 (CyclotomicField p ℚ)) = -d from by
        rw [hd, hcoe]; ring]
      exact hodd.neg_pow d
    rw [h1]
    exact (neg_dvd).mpr hdvd
  -- the K-level multiplier equation
  set f : 𝓞 (CyclotomicField p ℚ) →+* CyclotomicField p ℚ :=
    (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)) with hf
  have hfinj : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  have hN₂0 : N₂ ≠ 0 := factor_ne_zero_96 hζ hp hfer hx0 _ (zeta_pow_mem_96 hζ (a * (p - 1)))
  have hB0 : f N₂ ≠ 0 := fun h0 => hN₂0 (hfinj (by rw [h0, map_zero]))
  refine ⟨(f N₂) ^ (p - 1), pow_ne_zero _ hB0, a', ?_, hconv⟩
  rw [ha', map_mul, map_pow]
  rw [show ((f N₂) ^ (p - 1)) ^ p = (f N₂) ^ q from by
    rw [← pow_mul, mul_comm (p - 1) p]]
  rw [show (f N₂) ^ q = (f N₂) ^ (q - 1) * f N₂ from by
    rw [← pow_succ]; congr 1; omega]
  field_simp

/-! ### Item (c): the α p-th-power glue, and the 9.6/9.7 endgames -/

/-- **Washington Lemma 9.6, item (c)** — under Vandiver, the ratio
`α = (y − ζ^a z)/(y − ζ^{−a} z)` is a `p`-th power in `K`: its span is the
`p`-th power of the fractional ideal `A₁·A₂⁻¹` (item (a)), the wild multiplier
(item (c′)) makes the Kummer extension unramified, and the element-level
Lemma 9.2 (`cyclotomic_p_dvd_classNumber`) would contradict `p ∤ h⁺`. -/
theorem alpha_pth_power_96 [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hvand : IsVandiverPrime p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (hyz : IsCoprime y z) (a : ℕ) :
    ∃ w : CyclotomicField p ℚ, w ^ p
      = algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          ((y : 𝓞 (CyclotomicField p ℚ))
            - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)))
        / algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
          ((y : 𝓞 (CyclotomicField p ℚ))
            - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ))) := by
  classical
  set N₁ : 𝓞 (CyclotomicField p ℚ) :=
    (y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)) with hN₁
  set N₂ : 𝓞 (CyclotomicField p ℚ) :=
    (y : 𝓞 (CyclotomicField p ℚ))
      - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)) with hN₂
  set f : 𝓞 (CyclotomicField p ℚ) →+* CyclotomicField p ℚ :=
    (algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)) with hf
  have hfinj : Function.Injective f := FaithfulSMul.algebraMap_injective _ _
  have hN₁0 : N₁ ≠ 0 := factor_ne_zero_96 hζ hp hfer hx0 _ (zeta_pow_mem_96 hζ a)
  have hN₂0 : N₂ ≠ 0 := factor_ne_zero_96 hζ hp hfer hx0 _ (zeta_pow_mem_96 hζ (a * (p - 1)))
  have hF0 : f N₁ ≠ 0 := fun h0 => hN₁0 (hfinj (by rw [h0, map_zero]))
  have hB0 : f N₂ ≠ 0 := fun h0 => hN₂0 (hfinj (by rw [h0, map_zero]))
  set α : CyclotomicField p ℚ := f N₁ / f N₂ with hαdef
  have hα0 : α ≠ 0 := div_ne_zero hF0 hB0
  by_contra hcon
  push Not at hcon
  haveI hfact : Fact (Irreducible (X ^ p - C α)) :=
    ⟨X_pow_sub_C_irreducible_of_prime hpri.out hcon⟩
  -- the fractional-ideal p-th power
  obtain ⟨A₁, hA₁⟩ := exists_factor_ideals_96 hζ hp hfer hpy hpz hyz
    (hζ.toInteger ^ a) (zeta_pow_mem_96 hζ a)
  obtain ⟨A₂, hA₂⟩ := exists_factor_ideals_96 hζ hp hfer hpy hpz hyz
    (hζ.toInteger ^ (a * (p - 1))) (zeta_pow_mem_96 hζ (a * (p - 1)))
  set B₁ : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰ (CyclotomicField p ℚ) :=
    (A₁ : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰ (CyclotomicField p ℚ)) with hB₁def
  set B₂ : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰ (CyclotomicField p ℚ) :=
    (A₂ : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰ (CyclotomicField p ℚ)) with hB₂def
  have hcoe₁ : B₁ ^ p = FractionalIdeal.spanSingleton _ (f N₁) := by
    rw [hB₁def, ← FractionalIdeal.coeIdeal_pow, ← hA₁,
      FractionalIdeal.coeIdeal_span_singleton]
  have hcoe₂ : B₂ ^ p = FractionalIdeal.spanSingleton _ (f N₂) := by
    rw [hB₂def, ← FractionalIdeal.coeIdeal_pow, ← hA₂,
      FractionalIdeal.coeIdeal_span_singleton]
  have hB₂0 : B₂ ≠ 0 := by
    intro h0
    apply hB0
    have h2 : FractionalIdeal.spanSingleton
        ((𝓞 (CyclotomicField p ℚ))⁰) (f N₂) = 0 := by
      rw [← hcoe₂, h0, zero_pow (by omega : p ≠ 0)]
    rwa [FractionalIdeal.spanSingleton_eq_zero_iff] at h2
  have hcancel : B₂ * B₂⁻¹ = 1 := mul_inv_cancel₀ hB₂0
  set J : FractionalIdeal (𝓞 (CyclotomicField p ℚ))⁰ (CyclotomicField p ℚ) :=
    B₁ * B₂⁻¹ with hJ
  have hJ0 : J ≠ 0 := by
    intro h0
    apply hF0
    have h1 : B₁ = 0 := by
      calc B₁ = B₁ * (B₂⁻¹ * B₂) := by rw [inv_mul_cancel₀ hB₂0, mul_one]
        _ = J * B₂ := by rw [hJ]; ring
        _ = 0 := by rw [h0, zero_mul]
    have h2 : FractionalIdeal.spanSingleton
        ((𝓞 (CyclotomicField p ℚ))⁰) (f N₁) = 0 := by
      rw [← hcoe₁, h1, zero_pow (by omega : p ≠ 0)]
    rwa [FractionalIdeal.spanSingleton_eq_zero_iff] at h2
  have hspan : FractionalIdeal.spanSingleton _ α = J ^ p := by
    have hcancelp : B₂ ^ p * (B₂⁻¹) ^ p = 1 := by
      rw [← mul_pow, hcancel, one_pow]
    have h1 : FractionalIdeal.spanSingleton ((𝓞 (CyclotomicField p ℚ))⁰) α * B₂ ^ p
        = B₁ ^ p := by
      rw [hcoe₁, hcoe₂, FractionalIdeal.spanSingleton_mul_spanSingleton, hαdef,
        div_mul_cancel₀ _ hB0]
    calc FractionalIdeal.spanSingleton ((𝓞 (CyclotomicField p ℚ))⁰) α
        = FractionalIdeal.spanSingleton ((𝓞 (CyclotomicField p ℚ))⁰) α
          * (B₂ ^ p * (B₂⁻¹) ^ p) := by
          rw [hcancelp, mul_one]
      _ = (FractionalIdeal.spanSingleton ((𝓞 (CyclotomicField p ℚ))⁰) α * B₂ ^ p)
          * (B₂⁻¹) ^ p := by ring
      _ = B₁ ^ p * (B₂⁻¹) ^ p := by rw [h1]
      _ = J ^ p := by rw [hJ, mul_pow]
  -- wild multiplier and unramifiedness
  have hwild := wild_multiplier_96 hζ hp hfer hx0 hpy hpz a
  have hunram : IsUnramified (𝓞 (CyclotomicField p ℚ))
      (𝓞 (AdjoinRoot (X ^ p - C α))) :=
    isUnramified_adjoinRoot_of_pthRoot_data (by omega : p ≠ 2) hζ α J hJ0 hspan hwild
  -- conj α = α⁻¹
  have hτα : complexConj (CyclotomicField p ℚ) α = α⁻¹ := by
    have e1 : complexConj (CyclotomicField p ℚ) (f N₁) = f N₂ := by
      have hc1 : ringOfIntegersComplexConj (CyclotomicField p ℚ)
          ((y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)))
          = (y : 𝓞 (CyclotomicField p ℚ))
            - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)) :=
        conj_factor_96 hζ a
      rw [hN₁, hN₂, hf, ← NumberField.IsCMField.coe_ringOfIntegersComplexConj, hc1]
    have e2 : complexConj (CyclotomicField p ℚ) (f N₂) = f N₁ := by
      have hred : (a * (p - 1) * (p - 1)) % p = a % p := by
        have h2 := hpri.out.two_le
        have h3' : a * (p - 1) * (p - 1) = a * ((p - 1) * (p - 1)) := by ring
        have h4 : (p - 1) * (p - 1) = p * (p - 2) + 1 := by
          zify [show 1 ≤ p from by omega, show 2 ≤ p from h2]
          ring
        rw [h3', h4, show a * (p * (p - 2) + 1) = a + (a * (p - 2)) * p from by ring,
          Nat.add_mul_mod_self_right]
      have hc2 : ringOfIntegersComplexConj (CyclotomicField p ℚ)
          ((y : 𝓞 (CyclotomicField p ℚ))
            - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)))
          = (y : 𝓞 (CyclotomicField p ℚ)) - hζ.toInteger ^ a * (z : 𝓞 (CyclotomicField p ℚ)) := by
        have h3 : ringOfIntegersComplexConj (CyclotomicField p ℚ)
            ((y : 𝓞 (CyclotomicField p ℚ))
              - hζ.toInteger ^ (a * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)))
            = (y : 𝓞 (CyclotomicField p ℚ))
              - hζ.toInteger ^ (a * (p - 1) * (p - 1)) * (z : 𝓞 (CyclotomicField p ℚ)) :=
          conj_factor_96 hζ (a * (p - 1))
        rwa [Descent92.toInteger_pow_eq_of_mod hζ hred] at h3
      rw [hN₂, hN₁, hf, ← NumberField.IsCMField.coe_ringOfIntegersComplexConj, hc2]
    rw [hαdef, map_div₀, e1, e2, inv_div]
  -- Lemma 9.2 contradicts Vandiver
  have hvand' : ¬ p ∣ Fintype.card (ClassGroup
      (𝓞 (NumberField.maximalRealSubfield (CyclotomicField p ℚ)))) :=
    (Nat.Prime.coprime_iff_not_dvd hpri.out).mp hvand
  exact hvand' (cyclotomic_p_dvd_classNumber hp hα0 hτα hunram)

omit hpri [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)] in
/-- Auxiliary-prime bookkeeping: from `ℓ ≡ 1 (mod p)` and `ℓ < p² − p`,
write `ℓ = kp + 1` with `1 ≤ k < p − 1`. -/
theorem aux_k_96 {ℓ : ℕ} [hℓpri : Fact ℓ.Prime] (hp2 : 2 < p)
    (hℓ : ℓ % p = 1) (hsize : ℓ < p * p - p) :
    ℓ = (ℓ - 1) / p * p + 1 ∧ 1 ≤ (ℓ - 1) / p ∧ (ℓ - 1) / p < p - 1 := by
  have hℓ2 : 2 ≤ ℓ := hℓpri.out.two_le
  have hdvd : p ∣ ℓ - 1 := by
    have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt (by omega)
    have hmod : (1 : ℕ) ≡ ℓ [MOD p] := by
      unfold Nat.ModEq
      rw [h1, hℓ]
    exact (Nat.modEq_iff_dvd' (by omega)).mp hmod
  obtain ⟨k, hk⟩ := hdvd
  have hkval : (ℓ - 1) / p = k := by
    rw [hk]
    exact Nat.mul_div_cancel_left k (by omega)
  have hℓeq : ℓ = k * p + 1 := by
    rw [mul_comm]
    omega
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hk
      omega
    · exact h
  have hklt : k < p - 1 := by
    by_contra h
    push Not at h
    have h2 : (p - 1) * p ≤ k * p := Nat.mul_le_mul_right p h
    have e1 : k * p = ℓ - 1 := by
      rw [mul_comm]
      omega
    have e2 : (p - 1) * p = p * p - 1 * p := by
      rw [Nat.sub_mul]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hkval]
    exact hℓeq
  · rw [hkval]
    exact hk1
  · rw [hkval]
    exact hklt

/-- **Washington Lemma 9.6** — the auxiliary prime `ℓ = kp+1 < p² − p` divides
neither `y` (this statement) nor, by symmetry, `x`. -/
theorem lemma_9_6_not_dvd_y [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hvand : IsVandiverPrime p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (hyz : IsCoprime y z)
    {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime] (hℓ : ℓ % p = 1) (hsize : ℓ < p * p - p)
    (ht : redRoot p ℓ t ≠ 1) (ht0 : (t : ZMod ℓ) ≠ 0) :
    ¬ (ℓ : ℤ) ∣ y := by
  intro hly
  obtain ⟨hℓeq, hk1, hklt⟩ := aux_k_96 hp hℓ hsize
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓ ht ht0
  set φ : 𝓞 (CyclotomicField p ℚ) →ₐ[ℤ] ZMod ℓ := redHom hζ hμ with hφ
  -- ℓ ∤ z (coprimality with y)
  have hlz : ¬ (ℓ : ℤ) ∣ z := by
    intro hlz'
    obtain ⟨u, v, huv⟩ := hyz
    have h1 : (ℓ : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add (Dvd.dvd.mul_left hly u) (Dvd.dvd.mul_left hlz' v)
    have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have h3 := hℓpri.out.two_le
    omega
  have hzb : ((z : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hlz
  have hyb : ((y : ℤ) : ZMod ℓ) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hly
  -- the split at a = 1 and its reduction
  obtain ⟨γ, σ, hγreal, heq₁, heq₂⟩ := factor_split_96 hζ hp hvand hfer hx0 hpy hpz hyz 1
    (alpha_pth_power_96 hζ hp hvand hfer hx0 hpy hpz hyz 1)
  have hφY : φ ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((y : ℤ) : ZMod ℓ) := map_intCast φ y
  have hφZ : φ ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((z : ℤ) : ZMod ℓ) := map_intCast φ z
  have hφζ : φ hζ.toInteger = redRoot p ℓ t := redHom_zeta hζ hμ
  have he₁ : -(redRoot p ℓ t ^ 1 * ((z : ℤ) : ZMod ℓ))
      = φ ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * (φ σ) ^ p := by
    have h1 := congrArg φ heq₁
    rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ, hyb] at h1
    linear_combination h1
  have he₂ : -(redRoot p ℓ t ^ ((p - 1) * 1) * ((z : ℤ) : ZMod ℓ))
      = φ ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (φ (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ)) ^ p := by
    have h1 := congrArg φ heq₂
    rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ, hyb] at h1
    linear_combination h1
  -- nonvanishing of the σ-images
  have hμ0 : redRoot p ℓ t ≠ 0 := fun h0 => by
    have h1 := hμ.pow_eq_one
    rw [h0, zero_pow (by omega : p ≠ 0)] at h1
    exact zero_ne_one h1
  have hs₁ : φ σ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : p ≠ 0), mul_zero] at he₁
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hzb) (neg_eq_zero.mp he₁)
  have hs₂ : φ (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : p ≠ 0), mul_zero] at he₂
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hzb) (neg_eq_zero.mp he₂)
  exact lemma_9_6_zmod hpri.out hμ hp hklt (by omega) hzb
    (by
      intro hdvd
      have := Nat.le_of_dvd one_pos hdvd
      omega) hs₁ hs₂ he₁ he₂

/-- **Washington Lemma 9.7** — the auxiliary prime divides `z`. All the
`p`-th-power splits reduce mod a prime above `ℓ`; the shared-`γ` pairing feeds
`lemma_9_7_zmod`, whose binomial-sum cancellation forces `(z : ZMod ℓ) = 0`. -/
theorem lemma_9_7_dvd_z [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hvand : IsVandiverPrime p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z)
    (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime] (hℓ : ℓ % p = 1) (hsize : ℓ < p * p - p)
    (ht : redRoot p ℓ t ≠ 1) (ht0 : (t : ZMod ℓ) ≠ 0) :
    (ℓ : ℤ) ∣ z := by
  classical
  obtain ⟨hℓeq, hk1, hklt⟩ := aux_k_96 hp hℓ hsize
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓ ht ht0
  set φ : 𝓞 (CyclotomicField p ℚ) →ₐ[ℤ] ZMod ℓ := redHom hζ hμ with hφ
  have hφY : φ ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((y : ℤ) : ZMod ℓ) := map_intCast φ y
  have hφZ : φ ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((z : ℤ) : ZMod ℓ) := map_intCast φ z
  have hφX : φ ((x : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((x : ℤ) : ZMod ℓ) := map_intCast φ x
  have hφζ : φ hζ.toInteger = redRoot p ℓ t := redHom_zeta hζ hμ
  -- ℓ divides neither y nor x (Lemma 9.6, twice)
  have hly : ¬ (ℓ : ℤ) ∣ y :=
    lemma_9_6_not_dvd_y hζ hp hvand hfer hx0 hpy hpz hyz hℓ hsize ht ht0
  have hy0 : y ≠ 0 := fun h0 => hpy (h0 ▸ dvd_zero _)
  have hfer' : y ^ p + x ^ p = z ^ p := by linear_combination hfer
  have hlx : ¬ (ℓ : ℤ) ∣ x :=
    lemma_9_6_not_dvd_y hζ hp hvand hfer' hy0 hpx hpz hxz hℓ hsize ht ht0
  have hyb : ((y : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hly
  have hxb : ((x : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hlx
  -- no factor image vanishes
  have hfac : ∀ b : ℕ, φ ((y : 𝓞 (CyclotomicField p ℚ))
      - hζ.toInteger ^ b * (z : 𝓞 (CyclotomicField p ℚ))) ≠ 0 := by
    intro b h0
    have hmem := zeta_pow_mem_96 hζ (p := p) b
    have hdvd : ((y : 𝓞 (CyclotomicField p ℚ))
        - hζ.toInteger ^ b * (z : 𝓞 (CyclotomicField p ℚ)))
        ∣ ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
            ((y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ))) :=
      Finset.dvd_prod_of_mem
        (fun ζ' => (y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ))) hmem
    have h1 : φ (∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        ((y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ)))) = 0 := by
      have h2 := map_dvd φ hdvd
      rw [h0] at h2
      exact zero_dvd_iff.mp h2
    rw [prod_factors_96 hζ hp hfer, map_neg, map_pow, hφX, neg_eq_zero] at h1
    exact hxb (pow_eq_zero_iff (by omega : p ≠ 0) |>.mp h1)
  -- the per-index equations for the reduction lemma
  have heq : ∀ a ∈ Finset.range p, ∃ g s₁ s₂ : ZMod ℓ, s₁ ≠ 0 ∧ s₂ ≠ 0 ∧
      ((y : ℤ) : ZMod ℓ) - redRoot p ℓ t ^ a * ((z : ℤ) : ZMod ℓ) = g * s₁ ^ p
      ∧ ((y : ℤ) : ZMod ℓ) - redRoot p ℓ t ^ ((p - 1) * a) * ((z : ℤ) : ZMod ℓ)
        = g * s₂ ^ p := by
    intro a _
    obtain ⟨γ, σ, hγreal, heq₁, heq₂⟩ := factor_split_96 hζ hp hvand hfer hx0 hpy hpz hyz a
      (alpha_pth_power_96 hζ hp hvand hfer hx0 hpy hpz hyz a)
    refine ⟨φ ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)), φ σ,
      φ (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ), ?_, ?_, ?_, ?_⟩
    · intro h0
      apply hfac a
      have h1 := congrArg φ heq₁
      rw [map_mul, map_pow, h0, zero_pow (by omega : p ≠ 0), mul_zero] at h1
      exact h1
    · intro h0
      apply hfac (a * (p - 1))
      have h1 := congrArg φ heq₂
      rw [map_mul, map_pow, h0, zero_pow (by omega : p ≠ 0), mul_zero] at h1
      exact h1
    · have h1 := congrArg φ heq₁
      rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ] at h1
      linear_combination h1
    · have h1 := congrArg φ heq₂
      rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ] at h1
      linear_combination h1
  have hzb : ((z : ℤ) : ZMod ℓ) = 0 :=
    lemma_9_7_zmod hμ hk1 (by omega) hℓeq hyb heq
  have h2 : ((z : ℤ) : ZMod ℓ) = 0 ↔ (ℓ : ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z ℓ
  exact_mod_cast h2.mp hzb

end Factor96


/-! ### The top: Case II from the Boolean certificate alone -/

section Top

open CyclotomicNT FltVandiver FltVandiver.QiCert FltVandiver.Descent92
open NumberField NumberField.IsCMField Polynomial
open scoped NumberField

/-- **Case II of FLT via the 9.5 route, top level**: the single Boolean
certificate `vandiverCert p ℓ t (evenIndices p)` with `ℓ < p² − p` refutes any
oriented Case II solution — everything, including Vandiver at `p`, is decoded
from the one certificate. -/
theorem caseII_95_top {p ℓ t : ℕ} [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime]
    (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hsize : ℓ < p * p - p)
    {x y z : ℤ} (hxyz : x ^ p + y ^ p = z ^ p)
    (hz0 : z ≠ 0) (hpz : (p : ℤ) ∣ z) (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y)
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z) :
    False := by
  have hp2 : 2 < p := by omega
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  haveI : NumberField.IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (CyclotomicField p ℚ) (S := {p})
      ⟨p, Set.mem_singleton p, hp2⟩
  set ζ : CyclotomicField p ℚ := IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)
    with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  -- the certificate gives Vandiver…
  have hvand : IsVandiverPrime p := qiVandiverBridge_all hcert
  -- …and, decoded, the ℓ-data
  simp only [vandiverCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcert
  obtain ⟨⟨⟨⟨hℓp, htk⟩, ht1⟩, hke⟩, hQcert⟩ := hcert
  have hQlist : ∀ i ∈ evenIndices p, qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1 :=
    fun i hi => of_decide_eq_true (List.all_eq_true.mp hQcert i hi)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two (by omega))
  have hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1 := by
    intro i hiev hi2 hip
    obtain ⟨j, hj⟩ := hiev
    have hidx : i = 2 * ((j - 1) + 1) := by omega
    have hjlt : j - 1 < (p - 3) / 2 := by omega
    rw [hidx]
    exact hQlist _ (mem_evenIndices hpodd hjlt)
  -- ℓ-arithmetic
  have hℓ2 : 2 ≤ ℓ := hℓpri.out.two_le
  have ht0 : (t : ZMod ℓ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : ℓ - 1 ≠ 0)] at ht1
    exact zero_ne_one ht1
  have htred : redRoot p ℓ t ≠ 1 := htk
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓp htred ht0
  obtain ⟨hℓeq, hk1, hklt⟩ := aux_k_96 hp2 hℓp hsize
  have hℓk : ℓ - 1 = (ℓ - 1) / p * p := by omega
  -- Lemma 9.7 supplies the seed divisibility ℓ ∣ z
  have hx0 : x ≠ 0 := fun h0 => hpx (h0 ▸ dvd_zero _)
  have hℓz : (ℓ : ℤ) ∣ z :=
    lemma_9_7_dvd_z hζ hp2 hvand hxyz hx0 hpx hpy hpz hyz hxz hℓp hsize htred ht0
  exact caseII_95 hζ hp hvand hℓp hμ (k := (ℓ - 1) / p) hℓk hke hQall
    hxyz hz0 hpz hpx hpy hxy hxz hyz hℓz

/-- The single-orientation integer entry for the 9.5 route: `x^p + y^p = z^p`
with `p ∣ z`, `p ∤ y`, `x, y` coprime, `z ≠ 0` is impossible under the single
Boolean certificate. -/
theorem no_Int_Case2_95 {p ℓ t : ℕ} [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime]
    (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hsize : ℓ < p * p - p)
    {x y z : ℤ} (hcop : IsCoprime x y) (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z)
    (hz0 : z ≠ 0) (heq : x ^ p + y ^ p = z ^ p) : False := by
  have hppri : Nat.Prime p := Fact.out
  have hpne0 : p ≠ 0 := hppri.ne_zero
  have hpint : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hppri
  have hpx : ¬ (p : ℤ) ∣ x := by
    intro hdvd
    refine hpy (hpint.dvd_of_dvd_pow (n := p) ?_)
    have h1 : (p : ℤ) ∣ z ^ p - x ^ p :=
      dvd_sub (dvd_pow hpz hpne0) (dvd_pow hdvd hpne0)
    rwa [show z ^ p - x ^ p = y ^ p from by linear_combination -heq] at h1
  have hmix : ∀ {u v : ℤ}, (∀ q : ℤ, Prime q → q ∣ u → q ∣ v → False)
      → u ≠ 0 → IsCoprime u v := by
    intro u v hq hu
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    rcases Nat.eq_zero_or_pos (Int.gcd u v) with hg0 | hgpos
    · exact hu (Int.gcd_eq_zero_iff.mp hg0).1
    · obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqi : (q : ℤ) ∣ ((Int.gcd u v : ℕ) : ℤ) := by exact_mod_cast hqd
      exact hq _ (Nat.prime_iff_prime_int.mp hqp)
        (hqi.trans (Int.gcd_dvd_left u v)) (hqi.trans (Int.gcd_dvd_right u v))
  have hx0 : x ≠ 0 := by
    intro h0
    refine hpy (hpint.dvd_of_dvd_pow (n := p) ?_)
    have h1 : y ^ p = z ^ p := by
      rw [h0, zero_pow hpne0, zero_add] at heq
      exact heq
    rw [h1]
    exact dvd_pow hpz hpne0
  have hxz : IsCoprime x z := by
    refine hmix ?_ hx0
    intro q hq hqx hqz
    have h1 : q ∣ y ^ p := by
      rw [show y ^ p = z ^ p - x ^ p from by linear_combination heq]
      exact dvd_sub (dvd_pow hqz hpne0) (dvd_pow hqx hpne0)
    have h2 := hq.dvd_of_dvd_pow h1
    exact hq.not_unit (hcop.isUnit_of_dvd' hqx h2)
  have hyz : IsCoprime y z := by
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0] at hpy
      exact hpy (dvd_zero _)
    refine hmix ?_ hy0
    intro q hq hqy hqz
    have h1 : q ∣ x ^ p := by
      rw [show x ^ p = z ^ p - y ^ p from by linear_combination heq]
      exact dvd_sub (dvd_pow hqz hpne0) (dvd_pow hqy hpne0)
    have h2 := hq.dvd_of_dvd_pow h1
    exact hq.not_unit (hcop.isUnit_of_dvd' h2 hqy)
  exact caseII_95_top hp hcert hsize heq hz0 hpz hpx hpy hcop hxz hyz

/-- **Case II via the 9.5 route** (symmetric integer form): under the single
Boolean certificate, `a^p + b^p = c^p` with `gcd = 1`, `abc ≠ 0`, `p ∣ abc` is
impossible. -/
theorem caseII_95_int {p ℓ t : ℕ} [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime]
    (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hsize : ℓ < p * p - p)
    {a b c : ℤ} (hprod : a * b * c ≠ 0) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseII : (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  have hppri : Nat.Prime p := Fact.out
  have hpne0 : p ≠ 0 := hppri.ne_zero
  have hodd : Odd p := hppri.odd_of_ne_two (by omega)
  have hpint : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hppri
  have ha : a ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have hb : b ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have hc : c ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have div12 : ∀ q : ℤ, Prime q → q ∣ a → q ∣ b → q ∣ c := fun q hq hqa hqb => by
    have hd : q ∣ a ^ p + b ^ p := dvd_add (dvd_pow hqa hpne0) (dvd_pow hqb hpne0)
    rw [heq] at hd; exact hq.dvd_of_dvd_pow hd
  have div13 : ∀ q : ℤ, Prime q → q ∣ a → q ∣ c → q ∣ b := fun q hq hqa hqc => by
    have hd : q ∣ c ^ p - a ^ p := dvd_sub (dvd_pow hqc hpne0) (dvd_pow hqa hpne0)
    have hrw : c ^ p - a ^ p = b ^ p := by linear_combination -heq
    rw [hrw] at hd; exact hq.dvd_of_dvd_pow hd
  have div23 : ∀ q : ℤ, Prime q → q ∣ b → q ∣ c → q ∣ a := fun q hq hqb hqc => by
    have hd : q ∣ c ^ p - b ^ p := dvd_sub (dvd_pow hqc hpne0) (dvd_pow hqb hpne0)
    have hrw : c ^ p - b ^ p = a ^ p := by linear_combination -heq
    rw [hrw] at hd; exact hq.dvd_of_dvd_pow hd
  have hno_common : ∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b ∧ (q : ℤ) ∣ c)
      := by
    rintro q hqp ⟨hqa, hqb, hqc⟩
    have hqgcd : (q : ℤ) ∣ ({a, b, c} : Finset ℤ).gcd id := by
      apply Finset.dvd_gcd
      intros x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hqa
      · exact hqb
      · exact hqc
    rw [hgcd] at hqgcd
    have hu : IsUnit ((q : ℤ)) := isUnit_of_dvd_one hqgcd
    have hq1 : (q : ℤ) = 1 := by
      rcases Int.isUnit_iff.mp hu with h | h
      · exact h
      · have hge : (q : ℤ) ≥ 0 := Int.natCast_nonneg q
        omega
    have : q = 1 := by exact_mod_cast hq1
    exact hqp.one_lt.ne' this
  have coprime_of_div : ∀ {x y z : ℤ}, x ≠ 0 →
      (∀ q : ℤ, Prime q → q ∣ x → q ∣ y → q ∣ z) →
      (∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ x ∧ (q : ℤ) ∣ y ∧ (q : ℤ) ∣ z)) →
      IsCoprime x y := by
    intros x y z hx hdvdh hno
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    rcases Nat.eq_zero_or_pos (Int.gcd x y) with hz | hpos
    · exact hx (Int.gcd_eq_zero_iff.mp hz).1
    · obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqi : (q : ℤ) ∣ ((Int.gcd x y : ℕ) : ℤ) := by exact_mod_cast hqd
      have hqx : (q : ℤ) ∣ x := dvd_trans hqi (Int.gcd_dvd_left x y)
      have hqy : (q : ℤ) ∣ y := dvd_trans hqi (Int.gcd_dvd_right x y)
      have hqprime : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hqp
      have hqz : (q : ℤ) ∣ z := hdvdh _ hqprime hqx hqy
      exact hno q hqp ⟨hqx, hqy, hqz⟩
  have hab : IsCoprime a b := coprime_of_div ha div12 hno_common
  have hac : IsCoprime a c := coprime_of_div ha div13
    (fun q hq ⟨ha', hc', hb'⟩ => hno_common q hq ⟨ha', hb', hc'⟩)
  have hbc : IsCoprime b c := coprime_of_div hb div23
    (fun q hq ⟨hb', hc', ha'⟩ => hno_common q hq ⟨ha', hb', hc'⟩)
  rcases hpint.dvd_mul.mp hcaseII with hab' | hc'
  · rcases hpint.dvd_mul.mp hab' with hpa | hpb
    · have hpb : ¬ (p : ℤ) ∣ b := fun h => hpint.not_unit (hab.isUnit_of_dvd' hpa h)
      have heq' : c ^ p + (-b) ^ p = a ^ p := by
        rw [Odd.neg_pow hodd]; linear_combination -heq
      have hcop : IsCoprime c (-b) := (IsCoprime.symm hbc).neg_right
      have hnpb : ¬ (p : ℤ) ∣ (-b) := by rwa [dvd_neg]
      exact no_Int_Case2_95 hp hcert hsize hcop hnpb hpa ha heq'
    · have hpa : ¬ (p : ℤ) ∣ a := fun h => hpint.not_unit (hab.isUnit_of_dvd' h hpb)
      have heq' : (-a) ^ p + c ^ p = b ^ p := by
        rw [Odd.neg_pow hodd]; linear_combination -heq
      have hpc : ¬ (p : ℤ) ∣ c := fun h => hpint.not_unit (hbc.isUnit_of_dvd' hpb h)
      have hcop : IsCoprime (-a) c := hac.neg_left
      exact no_Int_Case2_95 hp hcert hsize hcop hpc hpb hb heq'
  · have hpb : ¬ (p : ℤ) ∣ b := fun h => hpint.not_unit (hbc.isUnit_of_dvd' h hc')
    exact no_Int_Case2_95 hp hcert hsize hab hpb hc' hc heq

/-- **The 9.5-route certificate engine, generic Case I**: FLT at `p` from the
single `Q_i` certificate (Case II) plus any proof of Case I.  This is the form
the `p = 2124679` campaign will instantiate (its Case I comes from the
Sophie-Germain auxiliary prime, not from Kummer 1857). -/
theorem fermatLastTheoremFor_of_certs_95'
    {p ℓ t : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hp5 : 5 ≤ p)
    (hQi : vandiverCert p ℓ t (evenIndices p) = true)
    (hsize : ℓ < p * p - p)
    (hcaseI : ∀ a b c : ℤ, ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p ≠ c ^ p) :
    FermatLastTheoremFor p := by
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc e
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime e hprod
  let d := ({a, b, c} : Finset ℤ).gcd id
  by_cases hcase : (p : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact caseII_95_int (by omega) hQi hsize hprod' hgcd hcase e'
  · exact hcaseI _ _ _ hcase e'

/-- **The 9.5-route certificate engine**: FLT at `p` from TWO certificates —
the all-even-index `Q_i` certificate at a single auxiliary pair `(ℓ, t)` with
`ℓ < p² − p`, and the irregular-index list with `p − 3` regular (Kummer 1857
Case I). -/
theorem fermatLastTheoremFor_of_certs_95
    {p ℓ t : ℕ} [Fact p.Prime] [Fact ℓ.Prime] {L : List ℕ}
    (hp5 : 5 ≤ p)
    (hQi : vandiverCert p ℓ t (evenIndices p) = true)
    (hsize : ℓ < p * p - p)
    (hirr : CyclotomicNT.QiCert.irrListCert p L = true)
    (hfree : (p - 3) ∉ L) :
    FermatLastTheoremFor p := by
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc e
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime e hprod
  let d := ({a, b, c} : Finset ℤ).gcd id
  by_cases hcase : (p : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact caseII_95_int (by omega) hQi hsize hprod' hgcd hcase e'
  · exact caseI_of_not_irregular hp5 (CyclotomicNT.QiCert.not_irregular_of_cert hirr hfree)
      hgcd hcase e'

end Top



end FltVandiver.Descent95
