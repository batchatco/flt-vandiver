import FltVandiver.Prop818Bridge

/-!
# Base independence of the `Q_i` test

`vandiverCert p ℓ t idx` takes a base `t`, a unit modulo `ℓ` that is not a `p`-th power, and
`μ = t^k` (`k = (ℓ − 1)/p`) is the primitive `p`-th root of unity in `ZMod ℓ` that the `Q_i`
formula uses. This file proves that the verdict at an even index does not depend on `t`.

With `k = 2m` and `g(c) = (μ^c − 1)^k · μ^{(p−1)mc}` (the last factor is `μ^{−mc}`),

  `Q_i^k = ∏_{b=1}^{(p−1)/2} g(b)^{b^e}`,  `e = p − 1 − i`.

The function `g` is `p`-periodic and even (`g(p − c) = g(c)`), so for even `e` the square of
`Q_i^k` is the same product over all of `𝔽_p^×`, on which `b ↦ rb` is a bijection. A second
valid base `t'` has `t'^k = μ^r` with `p ∤ r`, and its `g'` is `g(r·)`; reindexing gives

  `(Q_i(t')^k)^2 = ((Q_i(t)^k)^2)^{s^e}`,  `rs ≡ 1 (mod p)`,

and since everything lives in the group of `p`-th roots of unity with `p` odd,
`Q_i(t)^k = 1 ↔ Q_i(t')^k = 1` (`qi_pow_eq_one_iff_of_base`). Hence a passing certificate at
`evenIndices p` passes for every valid base (`vandiverCert_evenIndices_of_base`): a witness is a
pair `(p, ℓ)`, and the base is a convention of the evaluation. This is the mod-`𝔩` shadow of the
eigen-unit relation `σ_r(E_i) = E_i^{r^i}` up to `p`-th powers.
-/

namespace FltVandiver.QiCert

open Finset

section PowMod

variable {M : Type*} [Monoid M]

/-- For `x^p = 1`, powers of `x` depend only on the exponent modulo `p`. -/
theorem pow_mod_of_pow_eq_one {x : M} {p : ℕ} (hx : x ^ p = 1) (n : ℕ) :
    x ^ (n % p) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hx, one_pow, mul_one]

/-- For `x^p = 1`, exponents that agree in `ZMod p` give the same power. -/
theorem pow_eq_pow_of_cast_eq {x : M} {p : ℕ} (hx : x ^ p = 1) {a b : ℕ}
    (h : (a : ZMod p) = b) : x ^ a = x ^ b := by
  rw [← pow_mod_of_pow_eq_one hx a, ← pow_mod_of_pow_eq_one hx b]
  congr 1
  exact (ZMod.natCast_eq_natCast_iff' a b p).mp h

end PowMod

section Core

variable {ℓ : ℕ} [hℓpri : Fact ℓ.Prime] {p : ℕ}

/-- `g(c) = (μ^c − 1)^{2m} · μ^{(p−1)mc}`; the second factor is `μ^{−mc}` when `μ^p = 1`. -/
def gFun (p m : ℕ) (μ : ZMod ℓ) (c : ℕ) : ZMod ℓ :=
  (μ ^ c - 1) ^ (2 * m) * μ ^ ((p - 1) * m * c)

/-- The half-range product `∏_{b=1}^{(p−1)/2} g(b)^{b^e}`. -/
def halfProd (p m : ℕ) (μ : ZMod ℓ) (e : ℕ) : ZMod ℓ :=
  ∏ b ∈ Icc 1 ((p - 1) / 2), gFun p m μ b ^ (b ^ e)

/-- `g` is `p`-periodic. -/
theorem gFun_mod {μ : ZMod ℓ} (hμ : μ ^ p = 1) (m c : ℕ) :
    gFun p m μ (c % p) = gFun p m μ c := by
  unfold gFun
  rw [pow_mod_of_pow_eq_one hμ c]
  congr 1
  apply pow_eq_pow_of_cast_eq hμ
  push_cast
  rw [ZMod.natCast_mod]

/-- `g` is even: `g(p − c) = g(c)` for `c ≤ p`. -/
theorem gFun_p_sub {μ : ZMod ℓ} (hμ : μ ^ p = 1) (hp : 1 ≤ p) (m : ℕ) {c : ℕ} (hc : c ≤ p) :
    gFun p m μ (p - c) = gFun p m μ c := by
  unfold gFun
  have huv : μ ^ c * μ ^ (p - c) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hc, hμ]
  have h1 : μ ^ (p - c) - 1 = μ ^ (p - c) * (1 - μ ^ c) := by
    rw [mul_sub, mul_one, ← mul_comm (μ ^ c), huv]
  rw [h1, mul_pow, show (1 - μ ^ c) ^ (2 * m) = (μ ^ c - 1) ^ (2 * m) by
    rw [← neg_sub, Even.neg_pow ⟨m, by ring⟩]]
  have e := pow_eq_pow_of_cast_eq hμ (a := (p - c) * (2 * m) + (p - 1) * m * (p - c))
    (b := (p - 1) * m * c) (by
      push_cast [Nat.cast_sub hc, Nat.cast_sub hp]
      simp only [ZMod.natCast_self]
      ring)
  rw [← e]
  ring

/-- Each `g(c)`, `1 ≤ c < p`, is a `p`-th root of unity when `ℓ − 1 = 2mp`. -/
theorem gFun_pow_p {μ : ZMod ℓ} (hμ : IsPrimitiveRoot μ p) {m : ℕ} (hℓm : ℓ - 1 = 2 * m * p)
    {c : ℕ} (hc0 : 0 < c) (hcp : c < p) : gFun p m μ c ^ p = 1 := by
  unfold gFun
  have h1 : ((μ ^ c - 1) ^ (2 * m)) ^ p = 1 := by
    rw [← pow_mul, ← hℓm]
    exact ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr (hμ.pow_ne_one_of_pos_of_lt hc0.ne' hcp))
  have h2 : (μ ^ ((p - 1) * m * c)) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow]
  rw [mul_pow, h1, h2, mul_one]

/-- `Q_i^k` as the half-range product, for `k = 2m`, `t^k = μ`, `μ^p = 1`, `i < p`. -/
theorem qi_pow_eq_halfProd {t i : ℕ} {m : ℕ} (hk : (ℓ - 1) / p = 2 * m)
    (hμ : ((t : ZMod ℓ) ^ (2 * m)) ^ p = 1) (hip : i < p) :
    qi p i ℓ t ^ (2 * m) = halfProd p m ((t : ZMod ℓ) ^ (2 * m)) (p - 1 - i) := by
  have hinv : ((t : ZMod ℓ) ^ (2 * m))⁻¹ = ((t : ZMod ℓ) ^ (2 * m)) ^ (p - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 0 < p)]
    exact hμ
  have hd : 2 * m * dVal p i / 2 = m * dVal p i := by
    rw [mul_assoc]; exact Nat.mul_div_cancel_left _ (by norm_num)
  simp only [qi, halfProd, gFun]
  rw [hk, hd, mul_pow, ← prod_pow]
  simp only [mul_pow, prod_mul_distrib]
  rw [mul_comm]
  congr 1
  · apply prod_congr rfl
    intro b _
    ring
  · rw [show ((t : ZMod ℓ)⁻¹ ^ (m * dVal p i)) ^ (2 * m)
        = ((t : ZMod ℓ) ^ (2 * m))⁻¹ ^ (m * dVal p i) by
        rw [← pow_mul, mul_comm, pow_mul, inv_pow], hinv, ← pow_mul]
    simp only [← pow_mul]
    rw [prod_pow_eq_pow_sum]
    congr 1
    unfold dVal
    simp only [mul_sum]
    apply sum_congr rfl
    intro b _
    rw [show p - i = p - 1 - i + 1 by omega, pow_succ]
    ring

/-- For odd `p`, even `e`, and `μ` a primitive `p`-th root, the square of the half-range product
is the product over all of `1 ≤ b ≤ p − 1`. -/
theorem halfProd_sq {μ : ZMod ℓ} (hμ : IsPrimitiveRoot μ p) (hp : 3 ≤ p) (hpodd : p % 2 = 1)
    {m : ℕ} (hℓm : ℓ - 1 = 2 * m * p) {e : ℕ} (he : Even e) :
    halfProd p m μ e ^ 2 = ∏ b ∈ Icc 1 (p - 1), gFun p m μ b ^ (b ^ e) := by
  set h := (p - 1) / 2 with hh
  have hp2 : p = 2 * h + 1 := by omega
  set F : ℕ → ZMod ℓ := fun c => gFun p m μ c ^ (c ^ e) with hF
  have hIco : ∀ a b : ℕ, Ico a (b + 1) = Icc a b := fun a b => by
    ext x; simp only [mem_Ico, mem_Icc]; omega
  have hrefl : ∀ j, h + 1 ≤ j → j < p → F (p - j) = F j := by
    intro j hj1 hj2
    simp only [hF]
    rw [gFun_p_sub hμ.pow_eq_one (by omega) m (by omega)]
    apply pow_eq_pow_of_cast_eq (gFun_pow_p hμ hℓm (by omega) hj2)
    push_cast [Nat.cast_sub (by omega : j ≤ p)]
    simp only [ZMod.natCast_self, zero_sub]
    exact he.neg_pow _
  have hsplit : ∏ b ∈ Icc 1 (p - 1), F b = (∏ b ∈ Ico 1 (h + 1), F b) * ∏ b ∈ Ico (h + 1) p, F b := by
    rw [prod_Ico_consecutive F (by omega) (by omega), ← hIco 1 (p - 1),
      show p - 1 + 1 = p by omega]
  have hsecond : ∏ b ∈ Ico (h + 1) p, F b = ∏ b ∈ Ico 1 (h + 1), F b := by
    rw [show ∏ b ∈ Ico (h + 1) p, F b = ∏ b ∈ Ico (h + 1) p, F (p - b) from
      prod_congr rfl fun j hj => (hrefl j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2).symm,
      prod_Ico_reflect F (h + 1) (by omega : p ≤ p + 1)]
    congr 1
    ext b
    simp only [mem_Ico]
    omega
  show (∏ b ∈ Icc 1 h, F b) ^ 2 = ∏ b ∈ Icc 1 (p - 1), F b
  rw [hsplit, hsecond, ← hIco 1 h, sq]

/-- Reindexing the full product by `b ↦ rb`: for `rs ≡ 1 (mod p)`,
`∏_b g(rb)^{b^e} = (∏_c g(c)^{c^e})^{s^e}`. -/
theorem prod_gFun_mul_left {μ : ZMod ℓ} [hp : Fact p.Prime] (hμ : IsPrimitiveRoot μ p) {m : ℕ}
    (hℓm : ℓ - 1 = 2 * m * p) {r s : ℕ} (hrs : (r : ZMod p) * s = 1) (e : ℕ) :
    ∏ b ∈ Icc 1 (p - 1), gFun p m μ (r * b) ^ (b ^ e)
      = (∏ c ∈ Icc 1 (p - 1), gFun p m μ c ^ (c ^ e)) ^ (s ^ e) := by
  have hne : ∀ b : ℕ, b ∈ Icc 1 (p - 1) → (b : ZMod p) ≠ 0 := by
    intro b hb h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by simp at hb; omega) h0
    simp at hb; omega
  have hr0 : (r : ZMod p) ≠ 0 := by rintro h; rw [h, zero_mul] at hrs; exact zero_ne_one hrs
  have hs0 : (s : ZMod p) ≠ 0 := by rintro h; rw [h, mul_zero] at hrs; exact zero_ne_one hrs
  have hmem : ∀ x : ZMod p, x ≠ 0 → x.val ∈ Icc 1 (p - 1) := by
    intro x hx
    have := ZMod.val_lt x
    have : x.val ≠ 0 := fun h => hx ((ZMod.val_eq_zero x).mp h)
    simp only [mem_Icc]; omega
  rw [← prod_pow]
  refine prod_nbij' (fun b => ((r * b : ℕ) : ZMod p).val) (fun c => ((s * c : ℕ) : ZMod p).val)
    ?_ ?_ ?_ ?_ ?_
  · intro b hb
    apply hmem
    push_cast
    exact mul_ne_zero hr0 (hne b hb)
  · intro c hc
    apply hmem
    push_cast
    exact mul_ne_zero hs0 (hne c hc)
  · intro b hb
    try dsimp only
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_mul, ← mul_assoc, mul_comm (s : ZMod p),
      hrs, one_mul, ZMod.val_natCast, Nat.mod_eq_of_lt (by simp at hb; omega)]
  · intro c hc
    try dsimp only
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_mul, ← mul_assoc, hrs, one_mul,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by simp at hc; omega)]
  · intro b hb
    try dsimp only
    have hval : ((r * b : ℕ) : ZMod p).val = (r * b) % p := by rw [ZMod.val_natCast]
    rw [hval, ← gFun_mod hμ.pow_eq_one m (r * b), ← pow_mul, ← mul_pow]
    apply pow_eq_pow_of_cast_eq (gFun_pow_p hμ hℓm ?_ ?_)
    · push_cast
      rw [ZMod.natCast_mod, Nat.cast_mul]
      congr 1
      linear_combination (-(b : ZMod p)) * hrs
    · apply Nat.pos_of_ne_zero
      intro h0
      have h1 : ((r * b : ℕ) : ZMod p) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero h0
      push_cast at h1
      exact mul_ne_zero hr0 (hne b hb) h1
    · exact Nat.mod_lt _ hp.out.pos

/-- Changing `μ` to `μ^r` turns `g` into `g(r·)`. -/
theorem gFun_pow (p m : ℕ) (μ : ZMod ℓ) (r b : ℕ) :
    gFun p m (μ ^ r) b = gFun p m μ (r * b) := by
  unfold gFun
  rw [← pow_mul, ← pow_mul]
  congr 2
  ring

end Core

section Main

variable {p ℓ : ℕ} [hp : Fact p.Prime] [hℓpri : Fact ℓ.Prime]

/-- **Base independence of the `Q_i` test.** For two valid bases `t, t'` (units mod `ℓ` whose
`k`-th power is not `1`, `k = (ℓ−1)/p` even) and an even index `i < p`,
`Q_i(t)^k = 1 ↔ Q_i(t')^k = 1`. -/
theorem qi_pow_eq_one_iff_of_base {t t' i : ℕ} (hp2 : 2 < p) (hℓ : ℓ % p = 1)
    (htk : (t : ZMod ℓ) ^ ((ℓ - 1) / p) ≠ 1) (htu : (t : ZMod ℓ) ^ (ℓ - 1) = 1)
    (ht'k : (t' : ZMod ℓ) ^ ((ℓ - 1) / p) ≠ 1) (ht'u : (t' : ZMod ℓ) ^ (ℓ - 1) = 1)
    (hke : 2 ∣ (ℓ - 1) / p) (hi : Even i) (hip : i < p) :
    qi p i ℓ t ^ ((ℓ - 1) / p) = 1 ↔ qi p i ℓ t' ^ ((ℓ - 1) / p) = 1 := by
  obtain ⟨m, hm⟩ := hke
  have hpdvd : p ∣ ℓ - 1 := by
    have := Nat.div_add_mod ℓ p
    exact ⟨ℓ / p, by omega⟩
  have hℓm : ℓ - 1 = 2 * m * p := by rw [← hm, Nat.div_mul_cancel hpdvd]
  have hpodd : p % 2 = 1 := by rcases hp.out.eq_two_or_odd with h | h <;> omega
  -- the two primitive roots
  set μ : ZMod ℓ := (t : ZMod ℓ) ^ (2 * m) with hμdef
  set μ' : ZMod ℓ := (t' : ZMod ℓ) ^ (2 * m) with hμ'def
  have hμp : μ ^ p = 1 := by rw [hμdef, ← pow_mul, ← hℓm, htu]
  have hμ'p : μ' ^ p = 1 := by rw [hμ'def, ← pow_mul, ← hℓm, ht'u]
  have hμ1 : μ ≠ 1 := by rw [hμdef, ← hm]; exact htk
  have hμ'1 : μ' ≠ 1 := by rw [hμ'def, ← hm]; exact ht'k
  have hμ : IsPrimitiveRoot μ p := by
    have := IsPrimitiveRoot.orderOf μ
    rwa [orderOf_eq_prime hμp hμ1] at this
  have hμ' : IsPrimitiveRoot μ' p := by
    have := IsPrimitiveRoot.orderOf μ'
    rwa [orderOf_eq_prime hμ'p hμ'1] at this
  obtain ⟨r, hrp, hr⟩ := hμ.eq_pow_of_pow_eq_one hμ'p
  have hr0 : (r : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have : r = 0 := by
      rcases h with ⟨c, hc⟩
      rcases c with _ | c
      · simpa using hc
      · nlinarith [hp.out.two_le]
    subst this
    exact hμ'1 (by rw [← hr, pow_zero])
  set s : ℕ := ((r : ZMod p)⁻¹).val with hsdef
  have hrs : (r : ZMod p) * s = 1 := by
    rw [hsdef, ZMod.natCast_zmod_val, mul_inv_cancel₀ hr0]
  have hps : ¬ p ∣ s := by
    intro h
    rw [← ZMod.natCast_eq_zero_iff] at h
    rw [h, mul_zero] at hrs
    exact zero_ne_one hrs
  -- the two certificates as half-range products
  set e := p - 1 - i with he
  have hee : Even e := by
    obtain ⟨j, hj⟩ := hi
    rcases Nat.even_or_odd p with hpe | ⟨q, hq⟩
    · exact absurd (Nat.even_iff.mp hpe) (by omega)
    · exact ⟨q - j, by omega⟩
  have hR : qi p i ℓ t ^ ((ℓ - 1) / p) = halfProd p m μ e := by
    rw [hm]; exact qi_pow_eq_halfProd hm hμp hip
  have hR' : qi p i ℓ t' ^ ((ℓ - 1) / p) = halfProd p m μ' e := by
    rw [hm]; exact qi_pow_eq_halfProd hm hμ'p hip
  -- the key identity: (R')² = (R²)^(s^e)
  have hkey : halfProd p m μ' e ^ 2 = (halfProd p m μ e ^ 2) ^ (s ^ e) := by
    rw [halfProd_sq hμ' (by omega) hpodd hℓm hee, halfProd_sq hμ (by omega) hpodd hℓm hee, ← hr]
    rw [← prod_gFun_mul_left hμ hℓm hrs e]
    apply prod_congr rfl
    intro b _
    rw [gFun_pow]
  -- both sides are p-th roots of unity
  have hroot : ∀ ν : ZMod ℓ, IsPrimitiveRoot ν p → halfProd p m ν e ^ p = 1 := by
    intro ν hν
    unfold halfProd
    rw [← prod_pow]
    apply prod_eq_one
    intro b hb
    rw [← pow_mul, mul_comm, pow_mul, gFun_pow_p hν hℓm (by simp at hb; omega) (by simp at hb; omega),
      one_pow]
  have hRp := hroot μ hμ
  have hR'p := hroot μ' hμ'
  have h2p : Nat.gcd 2 p = 1 := by
    have : Nat.Coprime p 2 := hp.out.coprime_iff_not_dvd.mpr
      (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
    exact this.symm
  have hsp : Nat.gcd (s ^ e) p = 1 :=
    (Nat.Coprime.pow_right e (hp.out.coprime_iff_not_dvd.mpr hps)).symm
  rw [hR, hR']
  constructor
  · intro h1
    rw [h1, one_pow, one_pow] at hkey
    have := pow_gcd_eq_one.mpr ⟨hkey, hR'p⟩
    rwa [h2p, pow_one] at this
  · intro h1
    rw [h1, one_pow] at hkey
    have h2 : (halfProd p m μ e ^ 2) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hRp, one_pow]
    have := pow_gcd_eq_one.mpr ⟨hkey.symm, h2⟩
    rw [hsp, pow_one] at this
    have := pow_gcd_eq_one.mpr ⟨this, hRp⟩
    rwa [h2p, pow_one] at this

omit hp hℓpri in
/-- Every index of `evenIndices p` is even and below `p`. -/
theorem evenIndices_even_lt {i : ℕ} (hi : i ∈ evenIndices p) : Even i ∧ i < p := by
  simp only [evenIndices, List.mem_map, List.mem_range] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact ⟨⟨j + 1, by ring⟩, by omega⟩

/-- **A passing certificate passes for every valid base.** If `vandiverCert p ℓ t idx` holds
with every `i ∈ idx` even and below `p`, and `t'` is another valid base (`t'^{ℓ-1} = 1`,
`t'^k ≠ 1`), then `vandiverCert p ℓ t' idx` holds. -/
theorem vandiverCert_of_base {t t' : ℕ} {idx : List ℕ} (hp2 : 2 < p)
    (hcert : vandiverCert p ℓ t idx = true) (hidx : ∀ i ∈ idx, Even i ∧ i < p)
    (ht'k : (t' : ZMod ℓ) ^ ((ℓ - 1) / p) ≠ 1) (ht'u : (t' : ZMod ℓ) ^ (ℓ - 1) = 1) :
    vandiverCert p ℓ t' idx = true := by
  simp only [vandiverCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcert ⊢
  obtain ⟨⟨⟨⟨hℓ, htk⟩, htu⟩, hke⟩, hQ⟩ := hcert
  refine ⟨⟨⟨⟨hℓ, ht'k⟩, ht'u⟩, hke⟩, ?_⟩
  rw [List.all_eq_true] at hQ ⊢
  intro i hi
  have h1 := of_decide_eq_true (hQ i hi)
  apply decide_eq_true
  intro h2
  exact h1 ((qi_pow_eq_one_iff_of_base hp2 hℓ htk htu ht'k ht'u hke (hidx i hi).1
    (hidx i hi).2).mpr h2)

/-- **Base independence at `evenIndices p`.** A witness is a pair `(p, ℓ)`: the all-even
certificate, once it passes for one valid base, passes for every valid base. -/
theorem vandiverCert_evenIndices_of_base {t t' : ℕ} (hp2 : 2 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (ht'k : (t' : ZMod ℓ) ^ ((ℓ - 1) / p) ≠ 1) (ht'u : (t' : ZMod ℓ) ^ (ℓ - 1) = 1) :
    vandiverCert p ℓ t' (evenIndices p) = true :=
  vandiverCert_of_base hp2 hcert (fun _ hi => evenIndices_even_lt hi) ht'k ht'u

end Main

end FltVandiver.QiCert
