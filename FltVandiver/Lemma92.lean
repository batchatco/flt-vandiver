import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Tower
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Torsion
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Washington Lemma 9.2 — the conjugation-fixed unramified degree-`p` extension (D4)

This file builds the Galois-theoretic core of Washington's Lemma 9.2 for the Vandiver descent:
from minus-part Kummer data over a CM base, the radical extension `M = AdjoinRoot (Xᵖ - C α)` is
Galois over `K⁺` with group `C_p × C_2`, and the fixed field `L` of the conjugation `τ_M` is a
degree-`p` Galois extension of `K⁺`. Main results, increasing in concreteness:

* `exists_isGalois_finrank_eq` — abstract: over any `F ⊆ K` with `[K:F]=2` and an involution `τ`
  inverting a primitive `p`-th root `ζ` and the minus-part `α`.
* `cm_exists_isGalois_finrank_eq` — over any CM field `K` (`τ := complexConj K`,
  `K⁺ := maximalRealSubfield K`).
* `cyclotomic_exists_isGalois_finrank_eq` — over `K = ℚ(ζ_p)`; takes only the minus-part `α`.

Supporting pieces: the conjugation extension `conjExtend` (step 1) and Kummer generator `kummerAut`
(step 2) with their orders and commutativity; the ramification arithmetic
`ramificationIdx_dvd_finrank` / `ramificationIdx_dvd_of_tower` / `eq_one_of_dvd_two_of_dvd_odd`
(step 4 — proving `L/K⁺` unramified once `M/K` is, via the towers `K⁺ ⊆ L ⊆ M`, `K⁺ ⊆ K ⊆ M`).

What remains for the full Lemma 9.2 application lives with the descent: the minus-part `α` itself,
`M/K` unramified (Lemma 9.1, Kummer), and the class-number black box at `K⁺`. -/

open NumberField Ideal Polynomial

/-- For a Galois extension `L/K` of number fields, the ramification index of any prime over `q`
divides the degree `[L : K]`. Immediate from `e·f·g = n` (`ncard_primesOver_mul_…`) plus
`|Gal(L/K)| = [L:K]`. -/
theorem ramificationIdx_dvd_finrank {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {q : Ideal (𝓞 K)} [q.IsMaximal] (hq : q ≠ ⊥)
    {Q : Ideal (𝓞 L)} [Q.IsPrime] [Q.LiesOver q] :
    Ideal.ramificationIdx q Q ∣ Module.finrank K L := by
  have key := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (A := 𝓞 K) (B := 𝓞 L) (G := L ≃ₐ[K] L) (p := q)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx q Q (L ≃ₐ[K] L)] at key
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  rw [hcard] at key
  rw [← key hq]
  exact (dvd_mul_right _ _).mul_left _

/-- In a tower `T / S / R` of (torsion-free) Dedekind algebras, with primes `p ⊆ P ⊆ Q` lying over
each other, the ramification index of the bottom step divides that of the whole: `e(P|p) ∣ e(Q|p)`.
Immediate from multiplicativity `e(Q|p) = e(P|p)·e(Q|P)` (`ramificationIdx_algebra_tower'`). -/
theorem ramificationIdx_dvd_of_tower {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsDomain R] [IsDedekindDomain S] [IsDedekindDomain T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.IsTorsionFree R S] [Module.IsTorsionFree S T]
    (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p] :
    Ideal.ramificationIdx p P ∣ Ideal.ramificationIdx p Q := by
  rw [Ideal.ramificationIdx_algebra_tower' p P Q]
  exact dvd_mul_right _ _

/-- A number `e` dividing both `2` and an odd `p` is `1`. This kills the residual ramification:
`e(L/K⁺) ∣ 2` (from the CM tower) and `e(L/K⁺) ∣ p` (degree) with `p` odd force unramifiedness. -/
theorem eq_one_of_dvd_two_of_dvd_odd {e p : ℕ} (hodd : Odd p)
    (h2 : e ∣ 2) (hp : e ∣ p) : e = 1 := by
  have hgcd : Nat.gcd 2 p = 1 := Nat.coprime_two_left.mpr hodd
  have : e ∣ Nat.gcd 2 p := Nat.dvd_gcd h2 hp
  rwa [hgcd, Nat.dvd_one] at this

/-! ## D4 step 1 — extending conjugation to the radical extension

`M = K(α^{1/p}) = AdjoinRoot (Xᵖ - C α)`. Given a base automorphism `τ : K ≃ₐ[F] K` with the
minus-part condition `τ α = α⁻¹`, Washington Lemma 9.2 step 1 extends `τ` to `τ_M : M ≃ₐ[F] M`
sending the chosen root `β` to `β⁻¹` — legal because `τ(Xᵖ - C α) = Xᵖ - C α⁻¹` has `β⁻¹` as a root
(`(β⁻¹)ᵖ = (βᵖ)⁻¹ = α⁻¹ = τ α`). Built via `AdjoinRoot.liftAlgHom` + `AlgHom.bijective`. -/

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The root condition feeding `AdjoinRoot.liftAlgHom`: `β⁻¹` is a root of the `τ`-image of
`Xᵖ - C α`. Reduces to the minus-part hypothesis `τ α = α⁻¹`. -/
lemma conjExtend_eval₂ (τ : K ≃ₐ[F] K) {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))]
    (hτa : τ a = a⁻¹) :
    (X ^ p - C a).eval₂
      (↑((IsScalarTower.toAlgHom F K (AdjoinRoot (X ^ p - C a))).comp τ.toAlgHom) :
        K →+* AdjoinRoot (X ^ p - C a))
      (AdjoinRoot.root (X ^ p - C a))⁻¹ = 0 := by
  have hrp : AdjoinRoot.root (X ^ p - C a) ^ p
      = algebraMap K (AdjoinRoot (X ^ p - C a)) a := by
    have h0 := AdjoinRoot.eval₂_root (X ^ p - C a)
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
    rw [AdjoinRoot.algebraMap_eq]; exact h0
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, inv_pow, hrp]
  change (algebraMap K (AdjoinRoot (X ^ p - C a)) a)⁻¹
      - algebraMap K (AdjoinRoot (X ^ p - C a)) (τ a) = 0
  rw [hτa, map_inv₀]
  exact sub_self _

variable [FiniteDimensional F K]

/-- **Washington Lemma 9.2, step 1.** Extend a base automorphism `τ : K ≃ₐ[F] K` satisfying the
minus-part condition `τ α = α⁻¹` to `τ_M : M ≃ₐ[F] M` on `M = AdjoinRoot (Xᵖ - C α)`, sending the
chosen root to its inverse. -/
noncomputable def conjExtend (τ : K ≃ₐ[F] K) {p : ℕ} {a : K}
    [Fact (Irreducible (X ^ p - C a))] (hτa : τ a = a⁻¹) :
    AdjoinRoot (X ^ p - C a) ≃ₐ[F] AdjoinRoot (X ^ p - C a) :=
  have hfne : (X ^ p - C a : K[X]) ≠ 0 := (Fact.out (p := Irreducible (X ^ p - C a))).ne_zero
  letI : FiniteDimensional K (AdjoinRoot (X ^ p - C a)) :=
    (AdjoinRoot.powerBasis hfne).finite
  letI : FiniteDimensional F (AdjoinRoot (X ^ p - C a)) :=
    Module.Finite.trans K (AdjoinRoot (X ^ p - C a))
  AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom (X ^ p - C a)
      ((IsScalarTower.toAlgHom F K (AdjoinRoot (X ^ p - C a))).comp τ.toAlgHom)
      (AdjoinRoot.root (X ^ p - C a))⁻¹ (conjExtend_eval₂ τ hτa))
    (AlgHom.bijective _)

@[simp] lemma conjExtend_root (τ : K ≃ₐ[F] K) {p : ℕ} {a : K}
    [Fact (Irreducible (X ^ p - C a))] (hτa : τ a = a⁻¹) :
    conjExtend τ hτa (AdjoinRoot.root (X ^ p - C a)) = (AdjoinRoot.root (X ^ p - C a))⁻¹ := by
  simp only [conjExtend, AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_root]

@[simp] lemma conjExtend_algebraMap (τ : K ≃ₐ[F] K) {p : ℕ} {a : K}
    [Fact (Irreducible (X ^ p - C a))] (hτa : τ a = a⁻¹) (k : K) :
    conjExtend τ hτa (algebraMap K (AdjoinRoot (X ^ p - C a)) k)
      = algebraMap K (AdjoinRoot (X ^ p - C a)) (τ k) := by
  simp only [conjExtend, AlgEquiv.ofBijective_apply]
  rw [show algebraMap K (AdjoinRoot (X ^ p - C a)) k = AdjoinRoot.of (X ^ p - C a) k from rfl,
    AdjoinRoot.liftAlgHom_of]
  rfl

/-! ## D4 step 2 — `Gal(M/K⁺)` is abelian

The Kummer generator `σ : M ≃ₐ[K] M`, `σ β = ζ·β` (`ζᵖ = 1`), built by the same `liftAlgHom`
pattern over base `K`. It commutes with `τ_M` (`conjExtend`): checked on the generators `β` and
`algebraMap K`, both composites send `β ↦ ζ⁻¹·β⁻¹` (using `τ ζ = ζ⁻¹` and that `σ` fixes `K`).
Together with `τ_M² = id`, `⟨σ⟩` and `⟨τ_M⟩` generate an abelian `Gal(M/K⁺)`. -/

/-- `βᵖ = α` in `M = AdjoinRoot (Xᵖ - C α)`. -/
lemma root_pow_eq {p : ℕ} {a : K} :
    AdjoinRoot.root (X ^ p - C a) ^ p = algebraMap K (AdjoinRoot (X ^ p - C a)) a := by
  have h0 := AdjoinRoot.eval₂_root (X ^ p - C a)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
  rw [AdjoinRoot.algebraMap_eq]; exact h0

/-- Root condition for `σ`: `ζ·β` is a root of `Xᵖ - C α`, since `(ζβ)ᵖ = ζᵖβᵖ = α`. -/
lemma kummerAut_eval₂ {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))] {ζ : K} (hζp : ζ ^ p = 1) :
    (X ^ p - C a).eval₂ (↑(Algebra.ofId K (AdjoinRoot (X ^ p - C a))) : K →+* _)
      (algebraMap K (AdjoinRoot (X ^ p - C a)) ζ * AdjoinRoot.root (X ^ p - C a)) = 0 := by
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, mul_pow, ← map_pow, root_pow_eq, hζp, map_one, one_mul]
  exact sub_self _

/-- The Kummer generator `σ : M ≃ₐ[K] M`, `σ β = ζ·β`. -/
noncomputable def kummerAut {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))] {ζ : K}
    (hζp : ζ ^ p = 1) :
    AdjoinRoot (X ^ p - C a) ≃ₐ[K] AdjoinRoot (X ^ p - C a) :=
  have hfne : (X ^ p - C a : K[X]) ≠ 0 := (Fact.out (p := Irreducible (X ^ p - C a))).ne_zero
  letI : FiniteDimensional K (AdjoinRoot (X ^ p - C a)) :=
    (AdjoinRoot.powerBasis hfne).finite
  AlgEquiv.ofBijective
    (AdjoinRoot.liftAlgHom (X ^ p - C a) (Algebra.ofId K (AdjoinRoot (X ^ p - C a)))
      (algebraMap K (AdjoinRoot (X ^ p - C a)) ζ * AdjoinRoot.root (X ^ p - C a))
      (kummerAut_eval₂ hζp))
    (AlgHom.bijective _)

@[simp] lemma kummerAut_root {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))] {ζ : K}
    (hζp : ζ ^ p = 1) :
    kummerAut hζp (AdjoinRoot.root (X ^ p - C a))
      = algebraMap K (AdjoinRoot (X ^ p - C a)) ζ * AdjoinRoot.root (X ^ p - C a) := by
  simp only [kummerAut, AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_root]

/-- **Washington Lemma 9.2, step 2 (core).** `τ_M` and `σ` commute, so `Gal(M/K⁺)` is abelian. -/
lemma conjExtend_kummerAut_commute (τ : K ≃ₐ[F] K) {p : ℕ} {a : K}
    [Fact (Irreducible (X ^ p - C a))] {ζ : K} (hτa : τ a = a⁻¹) (hζp : ζ ^ p = 1)
    (hτζ : τ ζ = ζ⁻¹) (x : AdjoinRoot (X ^ p - C a)) :
    conjExtend τ hτa (kummerAut hζp x) = kummerAut hζp (conjExtend τ hτa x) := by
  have key : (conjExtend τ hτa).toAlgHom.toRingHom.comp (kummerAut hζp).toAlgHom.toRingHom
      = (kummerAut hζp).toAlgHom.toRingHom.comp (conjExtend τ hτa).toAlgHom.toRingHom := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext k
      change conjExtend τ hτa (kummerAut hζp (algebraMap K (AdjoinRoot (X ^ p - C a)) k))
        = kummerAut hζp (conjExtend τ hτa (algebraMap K (AdjoinRoot (X ^ p - C a)) k))
      simp only [AlgEquiv.commutes, conjExtend_algebraMap]
    · change conjExtend τ hτa (kummerAut hζp (AdjoinRoot.root (X ^ p - C a)))
        = kummerAut hζp (conjExtend τ hτa (AdjoinRoot.root (X ^ p - C a)))
      simp only [kummerAut_root, conjExtend_root, map_mul, map_inv₀, conjExtend_algebraMap, hτζ,
        mul_inv]
  exact congr($key x)

/-- `τ_M` is an involution when `τ` is (conjugation has order 2), so `⟨τ_M⟩` has order dividing 2.
On the generator: `τ_M(τ_M β) = τ_M(β⁻¹) = β`; on `K`: `τ_M² = τ² = id`. -/
lemma conjExtend_conjExtend (τ : K ≃ₐ[F] K) {p : ℕ} {a : K}
    [Fact (Irreducible (X ^ p - C a))] (hτa : τ a = a⁻¹) (hττ : ∀ k, τ (τ k) = k)
    (x : AdjoinRoot (X ^ p - C a)) :
    conjExtend τ hτa (conjExtend τ hτa x) = x := by
  have key : (conjExtend τ hτa).toAlgHom.toRingHom.comp (conjExtend τ hτa).toAlgHom.toRingHom
      = RingHom.id (AdjoinRoot (X ^ p - C a)) := by
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · ext k
      change conjExtend τ hτa (conjExtend τ hτa (algebraMap K (AdjoinRoot (X ^ p - C a)) k))
        = algebraMap K (AdjoinRoot (X ^ p - C a)) k
      simp only [conjExtend_algebraMap, hττ]
    · change conjExtend τ hτa (conjExtend τ hτa (AdjoinRoot.root (X ^ p - C a)))
        = AdjoinRoot.root (X ^ p - C a)
      simp only [conjExtend_root, map_inv₀, inv_inv]
  exact congr($key x)

/-- `τ_M` and `σ` (promoted to `M ≃ₐ[F] M` via `restrictScalars`) commute *as group elements* —
the group form of `conjExtend_kummerAut_commute`. With `σ` of order `p` and `τ_M` of order `2`, the
subgroup `⟨σ, τ_M⟩ ≤ (M ≃ₐ[F] M)` they generate is abelian (`≅ C_p × C_2`, order `2p`). -/
lemma conjExtend_commute_kummerAut (τ : K ≃ₐ[F] K) {p : ℕ} {a : K}
    [Fact (Irreducible (X ^ p - C a))] {ζ : K} (hτa : τ a = a⁻¹) (hζp : ζ ^ p = 1)
    (hτζ : τ ζ = ζ⁻¹) :
    Commute (conjExtend τ hτa) ((kummerAut hζp).restrictScalars F) := by
  change conjExtend τ hτa * (kummerAut hζp).restrictScalars F
    = (kummerAut hζp).restrictScalars F * conjExtend τ hτa
  ext x
  simp only [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
  exact conjExtend_kummerAut_commute τ hτa hζp hτζ x

/-- `τ_M ≠ 1` whenever `τ` moves some element of `K` (e.g. `τ ζ = ζ⁻¹ ≠ ζ` for `p > 2`), since
`τ_M` restricts to `τ` on `K`. With `τ_M² = 1` this gives `τ_M` order `2`. -/
lemma conjExtend_ne_one (τ : K ≃ₐ[F] K) {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))]
    (hτa : τ a = a⁻¹) {z : K} (hz : τ z ≠ z) :
    conjExtend τ hτa ≠ (1 : AdjoinRoot (X ^ p - C a) ≃ₐ[F] AdjoinRoot (X ^ p - C a)) := by
  intro h
  refine hz ?_
  have hcomm := conjExtend_algebraMap (p := p) τ hτa z
  rw [h, AlgEquiv.one_apply] at hcomm
  exact (FaithfulSMul.algebraMap_injective K (AdjoinRoot (X ^ p - C a)) hcomm).symm

/-- `σᵏ β = ζᵏ·β`. The action of the Kummer generator's powers on the root, by induction
(`σ` is `K`-linear so it fixes `algebraMap ζ`). Used to read off `orderOf σ = orderOf ζ = p`. -/
lemma kummerAut_pow_root {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))] {ζ : K}
    (hζp : ζ ^ p = 1) (k : ℕ) :
    (kummerAut hζp ^ k) (AdjoinRoot.root (X ^ p - C a))
      = algebraMap K (AdjoinRoot (X ^ p - C a)) (ζ ^ k) * AdjoinRoot.root (X ^ p - C a) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, AlgEquiv.mul_apply, kummerAut_root, map_mul, (kummerAut hζp ^ n).commutes,
      ih, ← mul_assoc, ← map_mul, ← pow_succ']

/-- `σᵖ = 1` (the `p`-th power of the Kummer generator is trivial), from `ζᵖ = 1`. -/
lemma kummerAut_pow_eq_one {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))] {ζ : K}
    (hζp : ζ ^ p = 1) :
    kummerAut hζp ^ p = (1 : AdjoinRoot (X ^ p - C a) ≃ₐ[K] AdjoinRoot (X ^ p - C a)) := by
  apply AlgEquiv.coe_algHom_injective
  ext
  simp only [AlgEquiv.coe_algHom, AlgEquiv.one_apply, kummerAut_pow_root, hζp, map_one, one_mul]

/-- `σ ≠ 1` when `ζ ≠ 1` (with `α ≠ 0`, `p ≠ 0`): `σ β = ζ·β ≠ β`. With `σᵖ = 1` and `p` prime
this pins `orderOf σ = p`. -/
lemma kummerAut_ne_one {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))] {ζ : K}
    (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) (ha : a ≠ 0) (hp0 : p ≠ 0) :
    kummerAut hζp ≠ (1 : AdjoinRoot (X ^ p - C a) ≃ₐ[K] AdjoinRoot (X ^ p - C a)) := by
  intro h
  have hr0 : AdjoinRoot.root (X ^ p - C a) ≠ 0 := by
    intro hr
    apply ha
    have h1 : algebraMap K (AdjoinRoot (X ^ p - C a)) a = 0 := by
      rw [← root_pow_eq, hr, zero_pow hp0]
    exact FaithfulSMul.algebraMap_injective K _ (h1.trans (map_zero _).symm)
  apply hζ1
  have hroot := kummerAut_root (p := p) (a := a) hζp
  rw [h, AlgEquiv.one_apply] at hroot
  have hone : algebraMap K (AdjoinRoot (X ^ p - C a)) ζ = 1 :=
    mul_right_cancel₀ hr0 (by rw [one_mul]; exact hroot.symm)
  exact FaithfulSMul.algebraMap_injective K _ (hone.trans (map_one _).symm)

/-- `orderOf σ = p` (`p` prime): `σᵖ = 1` and `σ ≠ 1`. -/
lemma orderOf_kummerAut {p : ℕ} [Fact p.Prime] {a : K} [Fact (Irreducible (X ^ p - C a))] {ζ : K}
    (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) (ha : a ≠ 0) :
    orderOf (kummerAut (a := a) hζp) = p :=
  orderOf_eq_prime (kummerAut_pow_eq_one (a := a) hζp)
    (kummerAut_ne_one hζp hζ1 ha (Fact.out (p := p.Prime)).pos.ne')

/-- `orderOf τ_M = 2` when `τ` is a nontrivial involution: `τ_M² = 1` and `τ_M ≠ 1`. -/
lemma orderOf_conjExtend (τ : K ≃ₐ[F] K) {p : ℕ} {a : K} [Fact (Irreducible (X ^ p - C a))]
    (hτa : τ a = a⁻¹) (hττ : ∀ k, τ (τ k) = k) {z : K} (hz : τ z ≠ z) :
    orderOf (conjExtend (p := p) τ hτa) = 2 := by
  have hsq : conjExtend (p := p) τ hτa ^ 2
      = (1 : AdjoinRoot (X ^ p - C a) ≃ₐ[F] AdjoinRoot (X ^ p - C a)) := by
    ext x
    rw [pow_two, AlgEquiv.mul_apply, AlgEquiv.one_apply]
    exact conjExtend_conjExtend τ hτa hττ x
  exact orderOf_eq_prime hsq (conjExtend_ne_one τ hτa hz)

-- NOTE: `[M:F] = 2p` CANNOT be a standalone lemma: its statement
-- `Module.finrank F (AdjoinRoot _) = 2p` needs `Module F (AdjoinRoot _)` COLD and fails (the warm
-- idiom rescues only proof *interiors*, not statements). So `[M:F]=2p` must be a `have` INSIDE the
-- single `IsGalois F M` proof (warm via `letI`s), then `[M:K]=p` (`adjoinRoot_powerBasis_dim` +
-- `PowerBasis.finrank`) × `[K:F]=2` (`Module.finrank_mul_finrank`). The final step-3 statement uses
-- `Module.finrank F L`, `L : IntermediateField F M` (clean) — never finrank on `AdjoinRoot`.

/-! ## D4 step 3 — degree backbone & Galois correspondence

Goal: `L := IntermediateField.fixedField (Subgroup.zpowers τ_M)` is Galois over `K⁺ = F` of degree
`p`. The instance wall (cold `Module.finrank K (AdjoinRoot _)`, see `adjoinRoot_powerBasis_dim`) is
NOT fatal — route through `PowerBasis`/warm bodies. Verified-to-exist Mathlib API for the rest:
* `[M:K] = p`: `(AdjoinRoot.powerBasis hfne).dim = p` + `PowerBasis.finrank` (warm).
* `[M:F] = 2p`: `Module.finrank_mul_finrank F K M` with `[K:F]=2` (warm body).
* `σ` and `τ_M` commute as group elements: `conjExtend_commute_kummerAut`. With orders `p`,
  `2` ⟹ `G = ⟨σ', τ_M⟩` abelian of order `2p` (needs ζ PRIMITIVE for `σ` order `p`; `τ_M² = 1`,
  `τ_M ≠ 1` from ζ ≠ ζ⁻¹).
* `IsGalois F M`: `IsGalois.of_card_aut_eq_finrank` (exhibit `card (M ≃ₐ[F] M) = 2p`) OR Artin
  `IsGalois.of_fixed_field` (fixed field of `G` = `F`).
* `IsGalois F L`, normal subgroup: `IsGalois.of_fixedField_normal_subgroup` (⟨τ_M⟩ normal since `G`
  abelian).
* `finrank F L = p`: `IntermediateField.finrank_fixedField_eq_card` gives `finrank L M = |⟨τ_M⟩| =
  2`, then tower law `finrank F M = finrank F L * finrank L M = 2p ⟹ finrank F L = p`.
The substantive obligations are the orders of σ/τ_M, `IsGalois F M`, and fixed-field = F. -/

section Degree
variable {K : Type*} [Field K]

/-- `[M : K] = p`, stated via the power-basis dimension. ROOT CAUSE of the earlier wall (from the
`synthInstance` trace): a COLD `Module.finrank K (AdjoinRoot (Xᵖ-C a))` in a statement makes the
elaborator repeatedly try `Field (AdjoinRoot _) ≟ Field K/F` against the local field instances and
backtrack — even though `Algebra K (AdjoinRoot _)` (via `AdjoinRoot.instAlgebra`) succeeds. The
`Module`/`Algebra.toModule` path won't fire cold; `maxSynthPendingDepth` is irrelevant. Robust:
route degrees through `PowerBasis`, and take `Module.finrank` only in a WARM body — after a
`letI : FiniteDimensional K M := (AdjoinRoot.powerBasis hfne).finite`, via `PowerBasis.finrank`. -/
lemma adjoinRoot_powerBasis_dim {p : ℕ} {a : K} (hfne : (X ^ p - C a : K[X]) ≠ 0) :
    (AdjoinRoot.powerBasis hfne).dim = p := by
  rw [AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

end Degree

/-- **Washington Lemma 9.2 — steps 1–4 assembled.** From conjugation-stable Kummer data over a CM
base (`τ α = α⁻¹`, `τ` a nontrivial involution, `ζ` a primitive `p`-th root with `τ ζ = ζ⁻¹`,
`[K:F]=2`, `p` an odd prime), the radical extension `M = AdjoinRoot (Xᵖ - C α)` is Galois over `F`
(group `C_p × C_2` of order `2p`), and the fixed field of `⟨τ_M⟩` is a degree-`p` Galois extension
of `F = K⁺` — the unramified-ready extension of Lemma 9.2. -/
theorem exists_isGalois_finrank_eq
    {p : ℕ} [Fact p.Prime] (hodd : Odd p) {a : K} [Fact (Irreducible (X ^ p - C a))] (ha : a ≠ 0)
    {ζ : K} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (τ : K ≃ₐ[F] K) (hτa : τ a = a⁻¹) (hττ : ∀ k, τ (τ k) = k) (hτζ : τ ζ = ζ⁻¹) (hzne : τ ζ ≠ ζ)
    (h2 : Module.finrank F K = 2) :
    ∃ L : IntermediateField F (AdjoinRoot (X ^ p - C a)),
      IsGalois F L ∧ Module.finrank F L = p := by
  have hfne : (X ^ p - C a : K[X]) ≠ 0 := (Fact.out (p := Irreducible (X ^ p - C a))).ne_zero
  -- warm the `Module _ (AdjoinRoot _)` instances (via `Algebra.toModule`, which only needs the
  -- cold-OK `Algebra _ (AdjoinRoot _)`) so the cold `Module`/`Algebra.toModule` synthesis that
  -- blocks `finrank`/`FiniteDimensional` of `M` resolves throughout this proof body.
  letI : Module K (AdjoinRoot (X ^ p - C a)) := Algebra.toModule
  letI : Module F (AdjoinRoot (X ^ p - C a)) := Algebra.toModule
  letI : FiniteDimensional K (AdjoinRoot (X ^ p - C a)) := (AdjoinRoot.powerBasis hfne).finite
  letI : FiniteDimensional F (AdjoinRoot (X ^ p - C a)) :=
    Module.Finite.trans K (AdjoinRoot (X ^ p - C a))
  let rs : (AdjoinRoot (X ^ p - C a) ≃ₐ[K] AdjoinRoot (X ^ p - C a)) →*
      (AdjoinRoot (X ^ p - C a) ≃ₐ[F] AdjoinRoot (X ^ p - C a)) :=
    { toFun := fun e => e.restrictScalars F
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  have hrs_inj : Function.Injective rs := by
    intro x y hxy; ext m; exact DFunLike.congr_fun hxy m
  set σ := kummerAut (a := a) hζp with hσ
  set τM := conjExtend (p := p) τ hτa with hτM
  have hσord : orderOf (rs σ) = p := by
    rw [orderOf_injective rs hrs_inj]; exact orderOf_kummerAut hζp hζ1 ha
  have hτord : orderOf τM = 2 := orderOf_conjExtend τ hτa hττ hzne
  have hcomm : Commute τM (rs σ) := conjExtend_commute_kummerAut τ hτa hζp hτζ
  set g := τM * rs σ with hg
  have hgord : orderOf g = 2 * p := by
    have hco : Nat.Coprime (orderOf τM) (orderOf (rs σ)) := by
      rw [hτord, hσord]; exact Nat.coprime_two_left.mpr hodd
    rw [hg, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hτord, hσord]
  have hMF : Module.finrank F (AdjoinRoot (X ^ p - C a)) = 2 * p := by
    rw [← Module.finrank_mul_finrank F K (AdjoinRoot (X ^ p - C a)), h2,
      (AdjoinRoot.powerBasis hfne).finrank, adjoinRoot_powerBasis_dim hfne]
  have hcardeq : Nat.card (AdjoinRoot (X ^ p - C a) ≃ₐ[F] AdjoinRoot (X ^ p - C a))
      = Module.finrank F (AdjoinRoot (X ^ p - C a)) := by
    refine le_antisymm ?_ ?_
    · rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le
    · rw [hMF, ← hgord]; exact orderOf_le_card
  haveI : IsGalois F (AdjoinRoot (X ^ p - C a)) := IsGalois.of_card_aut_eq_finrank F _ hcardeq
  have htop : Subgroup.zpowers g = ⊤ :=
    Subgroup.eq_top_of_card_eq (H := Subgroup.zpowers g)
      (by rw [Nat.card_zpowers, hgord, hcardeq, hMF])
  have hcomm_all : ∀ x y : AdjoinRoot (X ^ p - C a) ≃ₐ[F] AdjoinRoot (X ^ p - C a),
      x * y = y * x := by
    intro x y
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (htop.symm ▸ Subgroup.mem_top x)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (htop.symm ▸ Subgroup.mem_top y)
    rw [← zpow_add, add_comm, zpow_add]
  haveI hnorm : (Subgroup.zpowers τM).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [hcomm_all x n, mul_assoc, mul_inv_cancel, mul_one]; exact hn
  refine ⟨IntermediateField.fixedField (Subgroup.zpowers τM), inferInstance, ?_⟩
  have hLM : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers τM))
      (AdjoinRoot (X ^ p - C a)) = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hτord]
  have htower := Module.finrank_mul_finrank F
    (IntermediateField.fixedField (Subgroup.zpowers τM)) (AdjoinRoot (X ^ p - C a))
  rw [hLM, hMF] at htower
  omega

/-! ## D4 — concrete instantiation at a CM field

Specialize the abstract `exists_isGalois_finrank_eq` to a CM field `K` (e.g. `K = ℚ(ζ_p)`,
`K⁺ = maximalRealSubfield K`), discharging the field/conjugation/degree hypotheses from Mathlib's
CM API: `τ := complexConj K` (`K ≃ₐ[K⁺] K`, an involution by `complexConj_apply_apply`),
`[K⁺:K] = 2` by `IsQuadraticExtension.finrank_eq_two`. The minus-part data `α` (with
`complexConj K α = α⁻¹`, `Xᵖ - C α` irreducible) and the primitive root `ζ` (with
`complexConj K ζ = ζ⁻¹`) remain as inputs — these are produced by the descent (Washington §9.1) and
Lemma 9.1's Kummer construction. -/

section CMInstantiation
open NumberField NumberField.IsCMField

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

-- Shortcut instance: provide `Module (maximalRealSubfield K) ↥L` directly for any IntermediateField
-- `L` over `maximalRealSubfield K`, short-circuiting the long Subfield/Subalgebra/IntermediateField
-- typeclass search that otherwise blocks elaboration of `Module.finrank (maximalRealSubfield K) L`.
private instance maximalRealSubfield_module_intermediate
    {E : Type*} [Field E] [Algebra ↥(maximalRealSubfield K) E]
    (L : IntermediateField ↥(maximalRealSubfield K) E) :
    Module ↥(maximalRealSubfield K) ↥L := Algebra.toModule

/-- **Washington Lemma 9.2 over a CM field.** From minus-part Kummer data over a CM field `K`
(`complexConj K α = α⁻¹` with `Xᵖ - C α` irreducible, a primitive `p`-th root `ζ` with
`complexConj K ζ = ζ⁻¹`, `p` an odd prime), the fixed field of `⟨τ_M⟩` is a degree-`p` Galois
extension of `K⁺ = maximalRealSubfield K`. -/
theorem cm_exists_isGalois_finrank_eq
    {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    {ζ : K} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1) (hτζ : complexConj K ζ = ζ⁻¹)
    {a : K} [Fact (Irreducible (X ^ p - C a))] (ha : a ≠ 0) (hτa : complexConj K a = a⁻¹) :
    ∃ L : IntermediateField (maximalRealSubfield K) (AdjoinRoot (X ^ p - C a)),
      IsGalois (maximalRealSubfield K) L ∧
        Module.finrank (maximalRealSubfield K) L = p := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Fact.out (p := p.Prime)).ne_zero] at hζp
    exact one_ne_zero hζp.symm
  have hzne : complexConj K ζ ≠ ζ := by
    rw [hτζ]; intro h; apply hζ1
    have hsq : ζ ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [← h]; exact mul_inv_cancel₀ hζ0
    exact orderOf_eq_one_iff.mp (eq_one_of_dvd_two_of_dvd_odd hodd
      (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hζp))
  exact exists_isGalois_finrank_eq hodd ha hζp hζ1 (complexConj K) hτa
    (complexConj_apply_apply K) hτζ hzne (Algebra.IsQuadraticExtension.finrank_eq_two _ K)

end CMInstantiation

section Cyclotomic
open NumberField NumberField.IsCMField

/-- **Lemma 9.2 for the cyclotomic field** `K = ℚ(ζ_p)`, `K⁺ = ℚ(ζ_p)⁺`. The CM structure and the
canonical primitive root are supplied automatically; only the minus-part `α` (from the descent)
remains as input. -/
theorem cyclotomic_exists_isGalois_finrank_eq {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    [IsCMField (CyclotomicField p ℚ)]
    {a : CyclotomicField p ℚ} [Fact (Irreducible (X ^ p - C a))] (ha : a ≠ 0)
    (hτa : complexConj (CyclotomicField p ℚ) a = a⁻¹) :
    ∃ L : IntermediateField (maximalRealSubfield (CyclotomicField p ℚ)) (AdjoinRoot (X ^ p - C a)),
      IsGalois (maximalRealSubfield (CyclotomicField p ℚ)) L ∧
        Module.finrank (maximalRealSubfield (CyclotomicField p ℚ)) L = p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  set ζ : CyclotomicField p ℚ := IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  -- `ζ` as a torsion unit of `𝓞 K` (inlining flt-regular's `IsPrimitiveRoot.unit'`), to feed
  -- `complexConj_torsion : complexConj K ζ = ζ⁻¹`.
  have hτζ : complexConj (CyclotomicField p ℚ) ζ = ζ⁻¹ := by
    let u : (𝓞 (CyclotomicField p ℚ))ˣ :=
      { val := ⟨ζ, hζ.isIntegral (NeZero.pos p)⟩
        inv := ⟨ζ⁻¹, hζ.inv.isIntegral (NeZero.pos p)⟩
        val_inv := Subtype.ext <| mul_inv_cancel₀ <| hζ.ne_zero (NeZero.ne p)
        inv_val := Subtype.ext <| inv_mul_cancel₀ <| hζ.ne_zero (NeZero.ne p) }
    have hupow : u ^ p = 1 := by
      ext
      change ζ ^ p = 1
      exact hζ.pow_eq_one
    have hmem : u ∈ NumberField.Units.torsion (CyclotomicField p ℚ) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨p, NeZero.pos p, hupow⟩
    have huval : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) ↑u = ζ := rfl
    simpa [huval] using complexConj_torsion (CyclotomicField p ℚ)
      (⟨u, hmem⟩ : NumberField.Units.torsion (CyclotomicField p ℚ))
  exact cm_exists_isGalois_finrank_eq ((Fact.out : p.Prime).odd_of_ne_two (by omega))
    hζ.pow_eq_one (hζ.ne_one (by omega)) hτζ ha hτa

end Cyclotomic

/-! ## Toward the class-number contradiction

The fixed field `L/K⁺` is cyclic (degree `p` prime), the last instance needed — alongside
`IsUnramified (𝓞 K⁺) (𝓞 L)` (step 4) and `NumberField L` — to feed flt-regular's
`dvd_card_classGroup_of_isUnramified_isCyclic`, yielding `p ∣ h⁺` and contradicting Vandiver. -/

/-- A degree-`p` Galois extension (with `p` prime) has cyclic Galois group. -/
theorem isCyclic_aut_of_finrank_prime {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] {p : ℕ} [Fact p.Prime]
    (h : Module.finrank F E = p) : IsCyclic (E ≃ₐ[F] E) :=
  isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank, h])
