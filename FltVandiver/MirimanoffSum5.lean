import CyclotomicNT.MirimanoffSum

/-!
# The Mirimanoff sums `∑ j³tʲ` and `∑ j⁴tʲ` in `F_p` (brick 1 of the `B_{p-5}` Case I route)

Siblings of `CyclotomicNT.MirimanoffSum` (the `n = 3` / `S₂ = ∑ j²tʲ` endgame of Kummer's
`B_{p-3}` criterion), needed for the `n = 5` / `S₄ = ∑ j⁴tʲ` endgame of the `B_{p-5}` criterion.

Via the same finite telescoping + Fermat `tᵖ = t` mechanism, with the Eulerian numerators
`A₃ = t + 4t² + t³` and `A₄ = t + 11t² + 11t³ + t⁴ = t(1+t)(1+10t+t²)`:

  `(1−t)³ · ∑_{j<p} j³·tʲ = A₃(t)`,   `(1−t)⁴ · ∑_{j<p} j⁴·tʲ = A₄(t)`   (`t ≠ 1`).

`A₄` vanishes only at `t ∈ {0, −1}` and the roots of `1+10t+t²` (`= −5 ± 2√6`, present mod `p`
iff `6` is a QR).  Hence `∑ j⁴tʲ ≠ 0` for `t ∉ {0, 1, −1}` with `1+10t+t² ≠ 0` — the latter side
condition being *automatic* when `6` is a non-residue mod `p` (e.g. `p = 2124679`).

Reuses `MirimanoffSum.{sum_pow_eq_one, one_sub_mul_sum_mul_pow, one_sub_sq_mul_sum_sq_mul_pow}`.
Pure `ZMod p`; imports only, edits nothing.
-/

open Finset

namespace CyclotomicNT

variable {p : ℕ} [hpri : Fact p.Prime]

/-- **The Mirimanoff `S₃` closed form** (scaffold for `S₄`):
`(1−t)³·∑_{j<p} j³·tʲ = t + 4t² + t³` in `F_p`, `t ≠ 1`. -/
theorem one_sub_cube_mul_sum_cube_mul_pow {t : ZMod p} (ht : t ≠ 1) :
    (1 - t) ^ 3 * ∑ j ∈ Finset.range p, (j : ZMod p) ^ 3 * t ^ j = t + 4 * t ^ 2 + t ^ 3 := by
  have key : ∀ n : ℕ, (1 - t) * ∑ j ∈ Finset.range n, (j : ZMod p) ^ 3 * t ^ j
      = 3 * (∑ j ∈ Finset.range n, (j : ZMod p) ^ 2 * t ^ j)
        - 3 * (∑ j ∈ Finset.range n, (j : ZMod p) * t ^ j)
        + ((∑ j ∈ Finset.range n, t ^ j) - 1)
        - ((n : ZMod p) - 1) ^ 3 * t ^ n := by
    intro n
    induction n with
    | zero => simp; ring
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun j => (j : ZMod p) ^ 2 * t ^ j),
          Finset.sum_range_succ (f := fun j => (j : ZMod p) * t ^ j),
          Finset.sum_range_succ (f := fun j => t ^ j), mul_add, ih]
        push_cast
        ring
  have h := key p
  rw [sum_pow_eq_one ht, ZMod.pow_card, ZMod.natCast_self] at h
  have hS2 := one_sub_sq_mul_sum_sq_mul_pow ht
  have hS1 := one_sub_mul_sum_mul_pow ht
  linear_combination (1 - t) ^ 2 * h + 3 * hS2 - 3 * (1 - t) * hS1

/-- **The Mirimanoff `S₄` closed form**:
`(1−t)⁴·∑_{j<p} j⁴·tʲ = t + 11t² + 11t³ + t⁴` in `F_p`, `t ≠ 1`. -/
theorem one_sub_pow_four_mul_sum_quartic_mul_pow {t : ZMod p} (ht : t ≠ 1) :
    (1 - t) ^ 4 * ∑ j ∈ Finset.range p, (j : ZMod p) ^ 4 * t ^ j
      = t + 11 * t ^ 2 + 11 * t ^ 3 + t ^ 4 := by
  have key : ∀ n : ℕ, (1 - t) * ∑ j ∈ Finset.range n, (j : ZMod p) ^ 4 * t ^ j
      = 4 * (∑ j ∈ Finset.range n, (j : ZMod p) ^ 3 * t ^ j)
        - 6 * (∑ j ∈ Finset.range n, (j : ZMod p) ^ 2 * t ^ j)
        + 4 * (∑ j ∈ Finset.range n, (j : ZMod p) * t ^ j)
        - ((∑ j ∈ Finset.range n, t ^ j) - 1)
        - ((n : ZMod p) - 1) ^ 4 * t ^ n := by
    intro n
    induction n with
    | zero => simp; ring
    | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun j => (j : ZMod p) ^ 3 * t ^ j),
          Finset.sum_range_succ (f := fun j => (j : ZMod p) ^ 2 * t ^ j),
          Finset.sum_range_succ (f := fun j => (j : ZMod p) * t ^ j),
          Finset.sum_range_succ (f := fun j => t ^ j), mul_add, ih]
        push_cast
        ring
  have h := key p
  rw [sum_pow_eq_one ht, ZMod.pow_card, ZMod.natCast_self] at h
  have hS3 := one_sub_cube_mul_sum_cube_mul_pow ht
  have hS2 := one_sub_sq_mul_sum_sq_mul_pow ht
  have hS1 := one_sub_mul_sum_mul_pow ht
  linear_combination (1 - t) ^ 3 * h + 4 * hS3 - 6 * (1 - t) * hS2 + 4 * (1 - t) ^ 2 * hS1

/-- **Nonvanishing of the `S₄` sum**: for `t ∉ {0, 1, −1}` with `1+10t+t² ≠ 0`,
`∑_{j<p} j⁴·tʲ ≠ 0` in `F_p`.  (The last hypothesis is vacuous when `6` is a non-residue.) -/
theorem sum_quartic_mul_pow_ne_zero {t : ZMod p} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm1 : t ≠ -1)
    (hq : 1 + 10 * t + t ^ 2 ≠ 0) :
    ∑ j ∈ Finset.range p, (j : ZMod p) ^ 4 * t ^ j ≠ 0 := by
  intro hz
  have h := one_sub_pow_four_mul_sum_quartic_mul_pow (p := p) h1
  rw [hz, mul_zero] at h
  -- `0 = A₄(t) = t·(1+t)·(1+10t+t²)`
  have hfac : t * (1 + t) * (1 + 10 * t + t ^ 2) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp hfac with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact h0 h''
    · exact hm1 (by linear_combination h'')
  · exact hq h'

/-! ### Removing the side condition: the three-ratio lemma (`exists_good_ratio_5`)

The `hsix`/root-free shortcut is unnecessary. What replaces it is the classical fact that among a
Case I solution's three ratios (product `-1`), at least one avoids the roots of `1+10t+t²`, so a
usable Mirimanoff ratio always exists. This makes the `B_{p-5}` route unconditional in `6` and
covers every prime regular at `p-5` (e.g. `16843`, where `6` is a residue). -/

/-- The quadratic `X²+10X+1` has no root mod `11` (the one prime where the general argument's
`88` factor vanishes; `6` is a non-residue there, so this is where the roots fail to exist). -/
theorem no_quad_root_eleven : ∀ u : ZMod 11, u ^ 2 + 10 * u + 1 ≠ 0 := by decide

/-- **The three ratios of a Case I solution cannot all be roots of `1+10t+t²`.** With
`u₁u₂u₃ = -1` and each `uᵢ` a root, a contradiction follows (`w := u₁u₂` would satisfy
`w²-10w+1 = 0`, forcing `w = 1` when `u₁ ≠ u₂` and the impossible `88(10u₁+1) = 0` when `u₁ = u₂`;
the residual `p = 11` case is void since the quadratic has no root there). -/
theorem not_all_three_roots (hp7 : 7 ≤ p) {u₁ u₂ u₃ : ZMod p}
    (hu₁ : u₁ ≠ 0) (hprod : u₁ * u₂ * u₃ = -1)
    (h1 : u₁ ^ 2 + 10 * u₁ + 1 = 0) (h2 : u₂ ^ 2 + 10 * u₂ + 1 = 0)
    (h3 : u₃ ^ 2 + 10 * u₃ + 1 = 0) : False := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
      have := Nat.le_of_dvd (by norm_num) hd; omega
    simpa using this
  have h8ne : (8 : ZMod p) ≠ 0 := by
    rw [show (8 : ZMod p) = 2 ^ 3 by norm_num]; exact pow_ne_zero 3 h2ne
  -- `w := u₁u₂` satisfies `w² - 10w + 1 = 0`
  have hw2 : (u₁ * u₂) ^ 2 - 10 * (u₁ * u₂) + 1 = 0 := by
    linear_combination (u₁ * u₂) ^ 2 * h3 - (u₁ * u₂ * u₃ + 10 * u₁ * u₂ - 1) * hprod
  by_cases he : u₁ = u₂
  · rw [← he] at hw2
    have key : (88 : ZMod p) * (10 * u₁ + 1) = 0 := by
      linear_combination -hw2 + (u₁ ^ 2 - 10 * u₁ + 89) * h1
    by_cases hp11 : p = 11
    · subst hp11; exact no_quad_root_eleven u₁ h1
    · have h11ne : (11 : ZMod p) ≠ 0 := by
        have : ((11 : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd
          exact hp11 ((Nat.prime_dvd_prime_iff_eq hpri.out (by decide)).mp hd)
        simpa using this
      have h88ne : (88 : ZMod p) ≠ 0 := by
        rw [show (88 : ZMod p) = 8 * 11 by norm_num]; exact mul_ne_zero h8ne h11ne
      have hlin : 10 * u₁ + 1 = 0 := (mul_eq_zero.mp key).resolve_left h88ne
      have hu0 : u₁ ^ 2 = 0 := by linear_combination h1 - hlin
      exact hu₁ (pow_eq_zero_iff (by norm_num) |>.mp hu0)
  · have hf : (u₁ - u₂) * (u₁ + u₂ + 10) = 0 := by linear_combination h1 - h2
    have hs : u₁ + u₂ = -10 := by
      rcases mul_eq_zero.mp hf with h | h
      · exact absurd (sub_eq_zero.mp h) he
      · linear_combination h
    have hw1 : u₁ * u₂ = 1 := by linear_combination u₁ * hs - h1
    rw [hw1] at hw2
    exact h8ne (by linear_combination -hw2)

/-- The `{0, 1, −1}` conditions for a ratio `−a·b⁻¹` (extracted from `exists_good_ratio`). -/
private theorem ratio_ne_012 {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (hne : a ≠ b) : -a * b⁻¹ ≠ 0 ∧ -a * b⁻¹ ≠ 1 ∧ -a * b⁻¹ ≠ -1 := by
  have hd : -a * b⁻¹ = -(a / b) := by rw [div_eq_mul_inv]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact ha (neg_eq_zero.mp h)
    · exact hb (inv_eq_zero.mp h)
  · intro h
    rw [hd] at h
    have h2 : a / b = -1 := by linear_combination -h
    apply hab
    rw [div_eq_iff hb] at h2
    linear_combination h2
  · intro h
    rw [hd, neg_inj] at h
    exact hne ((div_eq_one_iff_eq hb).mp h)

/-- A pair `(a, b)` with `a + 2b = 0` has ratio `−a·b⁻¹ = 2`, which is fully good (avoids
`{0, 1, −1}` and the roots of `1+10t+t²`, since `1+20+4 = 25 ≠ 0` for `p ≠ 5`). -/
private theorem good_two (hp7 : 7 ≤ p) {a b : ZMod p} (hb : b ≠ 0) (hab2 : a + 2 * b = 0) :
    a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 ∧
      -a * b⁻¹ ≠ 0 ∧ -a * b⁻¹ ≠ 1 ∧ -a * b⁻¹ ≠ -1 ∧
      1 + 10 * (-a * b⁻¹) + (-a * b⁻¹) ^ 2 ≠ 0 := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
    simpa using this
  have h3ne : (3 : ZMod p) ≠ 0 := by
    have : ((3 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
    simpa using this
  have h5ne : (5 : ZMod p) ≠ 0 := by
    have : ((5 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
    simpa using this
  have ha : a = -(2 * b) := by linear_combination hab2
  have hr : -a * b⁻¹ = 2 := by rw [ha, neg_neg, mul_assoc, mul_inv_cancel₀ hb, mul_one]
  refine ⟨?_, hb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha]; exact neg_ne_zero.mpr (mul_ne_zero h2ne hb)
  · rw [show a + b = -b by rw [ha]; ring]; exact neg_ne_zero.mpr hb
  · rw [hr]; exact h2ne
  · rw [hr]; intro h; exact one_ne_zero (show (1 : ZMod p) = 0 by linear_combination h)
  · rw [hr]; intro h; exact h3ne (by linear_combination h)
  · rw [hr]; intro h
    have h5 : (5 : ZMod p) ^ 2 = 0 := by linear_combination h
    exact h5ne (pow_eq_zero_iff (by norm_num) |>.mp h5)

/-- **A Case I solution has a fully good Mirimanoff ratio for `S₄`**: one of the pairs
`(x,y), (y,z), (z,x)` has ratio `t = −a·b⁻¹ ∉ {0, 1, −1}` with `1+10t+t² ≠ 0` — no side condition
on `6`. This removes the `hsix` shortcut, so the `B_{p-5}` route works at every prime regular at
`p-5` (e.g. `16843`). -/
theorem exists_good_ratio_5 (hp7 : 7 ≤ p) {x y z : ZMod p} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hsum : x + y + z = 0) :
    ∃ a b : ZMod p, a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 ∧
      ((a = x ∧ b = y) ∨ (a = y ∧ b = z) ∨ (a = z ∧ b = x)) ∧
      -a * b⁻¹ ≠ 0 ∧ -a * b⁻¹ ≠ 1 ∧ -a * b⁻¹ ≠ -1 ∧
      1 + 10 * (-a * b⁻¹) + (-a * b⁻¹) ^ 2 ≠ 0 := by
  by_cases hxy : x = y
  · have hz2 : z + 2 * x = 0 := by linear_combination hsum + hxy
    obtain ⟨ha0, _, hab, c0, c1, cm1, cr⟩ := good_two hp7 hx hz2
    exact ⟨z, x, ha0, hx, hab, Or.inr (Or.inr ⟨rfl, rfl⟩), c0, c1, cm1, cr⟩
  · by_cases hyz : y = z
    · have hx2 : x + 2 * y = 0 := by linear_combination hsum + hyz
      obtain ⟨ha0, _, hab, c0, c1, cm1, cr⟩ := good_two hp7 hy hx2
      exact ⟨x, y, ha0, hy, hab, Or.inl ⟨rfl, rfl⟩, c0, c1, cm1, cr⟩
    · by_cases hzx : z = x
      · have hy2 : y + 2 * z = 0 := by linear_combination hsum + hzx
        obtain ⟨ha0, _, hab, c0, c1, cm1, cr⟩ := good_two hp7 hz hy2
        exact ⟨y, z, ha0, hz, hab, Or.inr (Or.inl ⟨rfl, rfl⟩), c0, c1, cm1, cr⟩
      · have hxyne : x + y ≠ 0 := fun h => hz (by linear_combination hsum - h)
        have hyzne : y + z ≠ 0 := fun h => hx (by linear_combination hsum - h)
        have hzxne : z + x ≠ 0 := fun h => hy (by linear_combination hsum - h)
        by_cases hr1 : 1 + 10 * (-x * y⁻¹) + (-x * y⁻¹) ^ 2 = 0
        · by_cases hr2 : 1 + 10 * (-y * z⁻¹) + (-y * z⁻¹) ^ 2 = 0
          · obtain ⟨c0, c1, cm1⟩ := ratio_ne_012 hz hx hzxne hzx
            refine ⟨z, x, hz, hx, hzxne, Or.inr (Or.inr ⟨rfl, rfl⟩), c0, c1, cm1, ?_⟩
            intro hr3
            have hprod : (-x * y⁻¹) * (-y * z⁻¹) * (-z * x⁻¹) = -1 := by field_simp
            exact not_all_three_roots hp7 (ratio_ne_012 hx hy hxyne hxy).1 hprod
              (by linear_combination hr1) (by linear_combination hr2) (by linear_combination hr3)
          · obtain ⟨c0, c1, cm1⟩ := ratio_ne_012 hy hz hyzne hyz
            exact ⟨y, z, hy, hz, hyzne, Or.inr (Or.inl ⟨rfl, rfl⟩), c0, c1, cm1, hr2⟩
        · obtain ⟨c0, c1, cm1⟩ := ratio_ne_012 hx hy hxyne hxy
          exact ⟨x, y, hx, hy, hxyne, Or.inl ⟨rfl, rfl⟩, c0, c1, cm1, hr1⟩

end CyclotomicNT
