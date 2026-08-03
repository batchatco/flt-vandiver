import FltVandiver.Prop818Bridge
import CyclotomicNT.EigenReindex
import CyclotomicNT.IndexReduction

/-!
# The Washington Theorem 9.5 route, core lemmas (UNCOMMITTED MODULE)

Lemma 9.8 (telescoping engine, per-hom and full-invariant forms), the
`pDlog`/`vandermonde_kill` combinatorial layer, the CRT joint-kernel of the
reduction homs, Galois equivariance of the certificates, and Lemma 9.9 with
its swap-point interface `assumption_II_95`.  See `CASEII95_PLAN.md` for the
ledger and design notes.
-/

namespace FltVandiver.Descent95

open Finset

variable {F : Type*} [Field F] {p : ℕ} {μ : F}

/-- Exponent transport: `μ^a` depends only on `a mod p`. -/
theorem mu_pow_transport (hμ : IsPrimitiveRoot μ p) {a b : ℕ} (h : a % p = b % p) :
    μ ^ a = μ ^ b := by
  calc μ ^ a = μ ^ (p * (a / p) + a % p) := by rw [Nat.div_add_mod]
    _ = (μ ^ p) ^ (a / p) * μ ^ (a % p) := by rw [pow_add, pow_mul]
    _ = μ ^ (a % p) := by rw [hμ.pow_eq_one, one_pow, one_mul]
    _ = μ ^ (b % p) := by rw [h]
    _ = (μ ^ p) ^ (b / p) * μ ^ (b % p) := by rw [hμ.pow_eq_one, one_pow, one_mul]
    _ = μ ^ (p * (b / p) + b % p) := by rw [pow_add, pow_mul]
    _ = μ ^ b := by rw [Nat.div_add_mod]

/-- The clean up-chain: if `1, 1+2j, …, 1+2sj` all avoid `0 mod p`, the
recurrence telescopes to `(1 − μ^{1+2sj})^k = μ^{sjk}·(1 − μ)^k`. -/
theorem chain_up {k j : ℕ}
    (hrec : ∀ c : ℕ, ¬ p ∣ c → ¬ p ∣ (c + 2 * j) →
      (1 - μ ^ (c + 2 * j)) ^ k = μ ^ (j * k) * (1 - μ ^ c) ^ k) :
    ∀ s : ℕ, (∀ s' ≤ s, ¬ p ∣ (1 + 2 * s' * j)) →
      (1 - μ ^ (1 + 2 * s * j)) ^ k = μ ^ (s * j * k) * (1 - μ) ^ k := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ n ih =>
    intro hclean
    have hstep : (1 - μ ^ (1 + 2 * n * j + 2 * j)) ^ k
        = μ ^ (j * k) * (1 - μ ^ (1 + 2 * n * j)) ^ k := by
      refine hrec _ (hclean n (by omega)) ?_
      have h1 := hclean (n + 1) le_rfl
      rwa [show 1 + 2 * (n + 1) * j = 1 + 2 * n * j + 2 * j from by ring] at h1
    have hih := ih (fun s' h => hclean s' (by omega))
    rw [show 1 + 2 * (n + 1) * j = 1 + 2 * n * j + 2 * j from by ring, hstep, hih,
      show (n + 1) * j * k = j * k + n * j * k from by ring, pow_add]
    ring

/-- The `j̃ := p − j` recurrence follows from the `j` recurrence by exponent
transport (`c + 2j̃ + 2j ≡ c mod p` and `μ^{j̃k}·μ^{jk} = μ^{pk} = 1`). -/
theorem hrec_flip (hμ : IsPrimitiveRoot μ p) {k j : ℕ} (hjp : j < p)
    (hrec : ∀ c : ℕ, ¬ p ∣ c → ¬ p ∣ (c + 2 * j) →
      (1 - μ ^ (c + 2 * j)) ^ k = μ ^ (j * k) * (1 - μ ^ c) ^ k) :
    ∀ c : ℕ, ¬ p ∣ c → ¬ p ∣ (c + 2 * (p - j)) →
      (1 - μ ^ (c + 2 * (p - j))) ^ k = μ ^ ((p - j) * k) * (1 - μ ^ c) ^ k := by
  intro c hc hc'
  have hend : (c + 2 * (p - j) + 2 * j) % p = c % p := by
    have h1 : c + 2 * (p - j) + 2 * j = c + 2 * p := by omega
    rw [h1, mul_comm 2 p]
    exact Nat.add_mul_mod_self_left c p 2
  have hcend : ¬ p ∣ (c + 2 * (p - j) + 2 * j) := by
    rw [Nat.dvd_iff_mod_eq_zero, hend, ← Nat.dvd_iff_mod_eq_zero]
    exact hc
  have h2 := hrec (c + 2 * (p - j)) hc' hcend
  rw [mu_pow_transport hμ hend] at h2
  -- h2 : (1 − μ^c)^k = μ^{jk}·(1 − μ^{c+2(p−j)})^k
  have h4 : μ ^ ((p - j) * k) * μ ^ (j * k) = 1 := by
    rw [← pow_add, ← Nat.add_mul, Nat.sub_add_cancel (le_of_lt hjp), pow_mul,
      hμ.pow_eq_one, one_pow]
  calc (1 - μ ^ (c + 2 * (p - j))) ^ k
      = 1 * (1 - μ ^ (c + 2 * (p - j))) ^ k := (one_mul _).symm
    _ = (μ ^ ((p - j) * k) * μ ^ (j * k)) * (1 - μ ^ (c + 2 * (p - j))) ^ k := by rw [h4]
    _ = μ ^ ((p - j) * k) * (μ ^ (j * k) * (1 - μ ^ (c + 2 * (p - j))) ^ k) := by ring
    _ = μ ^ ((p - j) * k) * (1 - μ ^ c) ^ k := by rw [← h2]

/-- One clean chain delivers the `b`-instance with the intrinsic exponent. -/
theorem chain_endpoint (hpp : p.Prime) (hp : 2 < p) (hμ : IsPrimitiveRoot μ p)
    {k j b : ℕ} (hb : ¬ p ∣ b)
    (hrec : ∀ c : ℕ, ¬ p ∣ c → ¬ p ∣ (c + 2 * j) →
      (1 - μ ^ (c + 2 * j)) ^ k = μ ^ (j * k) * (1 - μ ^ c) ^ k)
    (s : ℕ) (hs : (1 + 2 * s * j) % p = b % p)
    (hclean : ∀ s' ≤ s, ¬ p ∣ (1 + 2 * s' * j)) :
    (1 - μ ^ b) ^ k = μ ^ (k * (b - 1) * ((p + 1) / 2)) * (1 - μ) ^ k := by
  have hchain := chain_up hrec s hclean
  rw [mu_pow_transport hμ hs] at hchain
  rw [hchain]
  congr 1
  -- μ^{sjk} = μ^{k(b−1)(p+1)/2}: from 2sj ≡ b − 1 mod p
  apply mu_pow_transport hμ
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · exact absurd (dvd_zero p) hb
    · exact h
  have hmodeq : 2 * s * j ≡ b - 1 [MOD p] := by
    have h1 : 2 * s * j + 1 ≡ (b - 1) + 1 [MOD p] := by
      unfold Nat.ModEq
      rw [show (b - 1) + 1 = b from by omega, show 2 * s * j + 1 = 1 + 2 * s * j from by ring]
      exact hs
    exact Nat.ModEq.add_right_cancel' 1 h1
  have h3 := hmodeq.mul_right (k * ((p + 1) / 2))
  have hodd : 2 * ((p + 1) / 2) = p + 1 := by
    have := hpp.odd_of_ne_two (by omega)
    rw [Nat.odd_iff] at this
    omega
  have h4 : 2 * s * j * (k * ((p + 1) / 2)) = s * j * k * (2 * ((p + 1) / 2)) := by ring
  have h5 : (b - 1) * (k * ((p + 1) / 2)) = k * (b - 1) * ((p + 1) / 2) := by ring
  rw [h4, hodd, h5] at h3
  have h6 : s * j * k * (p + 1) ≡ s * j * k [MOD p] := by
    have h7 : s * j * k * (p + 1) = s * j * k + (s * j * k) * p := by ring
    unfold Nat.ModEq
    rw [h7]
    exact Nat.add_mul_mod_self_right _ _ _
  exact h6.symm.trans h3

/-- **The telescoping engine (Lemma 9.8, combinatorial core).** From the
`2j`-step recurrence with both endpoints `≢ 0 (mod p)`, every `b ≢ 0` satisfies
`(1 − μ^b)^k = μ^{k(b−1)(p+1)/2}·(1 − μ)^k`. -/
theorem telescope_main (hpp : p.Prime) (hp : 2 < p) (hμ : IsPrimitiveRoot μ p)
    {k j : ℕ} (hjp : j < p) (hj0 : 0 < j)
    (hrec : ∀ c : ℕ, ¬ p ∣ c → ¬ p ∣ (c + 2 * j) →
      (1 - μ ^ (c + 2 * j)) ^ k = μ ^ (j * k) * (1 - μ ^ c) ^ k) :
    ∀ b : ℕ, ¬ p ∣ b →
      (1 - μ ^ b) ^ k = μ ^ (k * (b - 1) * ((p + 1) / 2)) * (1 - μ) ^ k := by
  intro b hb
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  set J : ZMod p := (j : ZMod p) with hJ
  set B : ZMod p := (b : ZMod p) with hB
  have hvalcast : ∀ a : ZMod p, ((a.val : ℕ) : ZMod p) = a := fun a =>
    ZMod.natCast_zmod_val a
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h1 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      exact fun hdvd => absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
    exact_mod_cast h1
  have hJne : J ≠ 0 := by
    rw [hJ, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    exact fun hdvd => absurd (Nat.le_of_dvd hj0 hdvd) (by omega)
  have hBne : B ≠ 0 := by
    rw [hB, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    exact hb
  have h2Jne : (2 : ZMod p) * J ≠ 0 := mul_ne_zero h2ne hJne
  set σ₀ : ZMod p := -((2 : ZMod p) * J)⁻¹ with hσ₀
  set σb : ZMod p := (B - 1) * ((2 : ZMod p) * J)⁻¹ with hσb
  have hσ₀ne : σ₀ ≠ 0 := by
    rw [hσ₀, neg_ne_zero]
    exact inv_ne_zero h2Jne
  have hσbmul : σb * ((2 : ZMod p) * J) = B - 1 := by
    rw [hσb, mul_assoc, inv_mul_cancel₀ h2Jne, mul_one]
  have hσne : σb ≠ σ₀ := by
    intro h
    apply hBne
    have h1 : σ₀ * ((2 : ZMod p) * J) = -1 := by
      rw [hσ₀, neg_mul, inv_mul_cancel₀ h2Jne]
    rw [h, h1] at hσbmul
    linear_combination -hσbmul
  -- the generic one-chain step, parametric in j'
  have main : ∀ j' : ℕ, 0 < j' → j' < p →
      (∀ c : ℕ, ¬ p ∣ c → ¬ p ∣ (c + 2 * j') →
        (1 - μ ^ (c + 2 * j')) ^ k = μ ^ (j' * k) * (1 - μ ^ c) ^ k) →
      ∀ s : ℕ, (1 + 2 * (s : ZMod p) * (j' : ZMod p)) = B →
        s < (-((2 : ZMod p) * (j' : ZMod p))⁻¹).val →
        (1 - μ ^ b) ^ k = μ ^ (k * (b - 1) * ((p + 1) / 2)) * (1 - μ) ^ k := by
    intro j' hj'0 hj'p hrec' s hsB hslt
    have hj'ne : ((j' : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      exact fun h => absurd (Nat.le_of_dvd hj'0 h) (by omega)
    have h2j' : (2 : ZMod p) * (j' : ZMod p) ≠ 0 := mul_ne_zero h2ne hj'ne
    refine chain_endpoint hpp hp hμ hb hrec' s ?_ ?_
    · -- (1+2sj') % p = b % p
      have h1 : ((1 + 2 * s * j' : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) := by
        push_cast
        rw [← hB]
        linear_combination hsB
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
    · intro s' hs'le hdvd
      have h1 : ((1 + 2 * s' * j' : ℕ) : ZMod p) = 0 := by
        rw [CharP.cast_eq_zero_iff (ZMod p) p]
        exact hdvd
      push_cast at h1
      have h3 : ((s' : ℕ) : ZMod p) * ((2 : ZMod p) * (j' : ZMod p)) = -1 := by
        linear_combination h1
      have h4 : ((s' : ℕ) : ZMod p) = -1 * ((2 : ZMod p) * (j' : ZMod p))⁻¹ := by
        calc ((s' : ℕ) : ZMod p)
            = ((s' : ℕ) : ZMod p) * (((2 : ZMod p) * (j' : ZMod p))
              * ((2 : ZMod p) * (j' : ZMod p))⁻¹) := by
              rw [mul_inv_cancel₀ h2j', mul_one]
          _ = (((s' : ℕ) : ZMod p) * ((2 : ZMod p) * (j' : ZMod p)))
              * ((2 : ZMod p) * (j' : ZMod p))⁻¹ := by ring
          _ = -1 * ((2 : ZMod p) * (j' : ZMod p))⁻¹ := by rw [h3]
      rw [neg_one_mul] at h4
      have h5 : s' % p = (-((2 : ZMod p) * (j' : ZMod p))⁻¹).val := by
        rw [← h4, ZMod.val_natCast]
      have hvlt : (-((2 : ZMod p) * (j' : ZMod p))⁻¹).val < p := ZMod.val_lt _
      have hs'p : s' < p := by omega
      rw [Nat.mod_eq_of_lt hs'p] at h5
      omega
  -- pigeonhole: pick the clean chain
  rcases lt_or_ge σb.val σ₀.val with hlt | hge
  · -- up-chain with j, s := σb.val
    refine main j hj0 hjp hrec σb.val ?_ ?_
    · rw [hvalcast σb, ← hJ]
      linear_combination hσbmul
    · rw [← hJ, ← hσ₀]
      exact hlt
  · -- flip chain with j̃ := p − j, s := (−σb).val
    have hj'0 : 0 < p - j := by omega
    have hj'p : p - j < p := by omega
    have hJ' : ((p - j : ℕ) : ZMod p) = -J := by
      have h1 : ((p - j : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) - ((j : ℕ) : ZMod p) := by
        have h2 : ((p - j) : ℕ) + j = p := by omega
        have h3 := congrArg (fun t : ℕ => ((t : ℕ) : ZMod p)) h2
        push_cast at h3
        linear_combination h3
      rw [h1, ZMod.natCast_self, zero_sub, hJ]
    -- strict val inequality on the negatives
    have hσbne0 : σb ≠ 0 := by
      intro h0
      have h1 : σ₀.val = 0 := by
        rw [h0, ZMod.val_zero] at hge
        omega
      exact hσ₀ne ((ZMod.val_eq_zero _).mp h1)
    have hnegb : (-σb).val = p - σb.val := by
      rw [ZMod.neg_val]
      simp [hσbne0]
    have hneg0 : (-σ₀).val = p - σ₀.val := by
      rw [ZMod.neg_val]
      simp [hσ₀ne]
    have hvalne : σb.val ≠ σ₀.val := fun h => hσne (ZMod.val_injective p h)
    have hσblt : σb.val < p := ZMod.val_lt _
    have hneglt : (-σb).val < (-σ₀).val := by omega
    refine main (p - j) hj'0 hj'p (hrec_flip hμ hjp hrec) (-σb).val ?_ ?_
    · rw [hvalcast (-σb), hJ']
      linear_combination hσbmul
    · rw [hJ']
      have h1 : -((2 : ZMod p) * -J)⁻¹ = -σ₀ := by
        rw [hσ₀, mul_neg, inv_neg]
      rw [h1]
      exact hneglt

/-! ### Layers 2–3 and the assembly of Lemma 9.8 -/

section Assembly

variable {p : ℕ} [hpri : Fact p.Prime] {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime]

open CyclotomicNT FltVandiver FltVandiver.QiCert
open scoped NumberField

/-- **Layer 2**: the step recurrence, derived from the reduced descent
equations. `w = φω`, `th = φθ`, `μ = φζ`; `j` is the vanishing-factor index
(`w = −μ^j·th`). At centers `≡ 0 mod p` the recurrence is a direct identity. -/
theorem hrec_of_equations {μ : ZMod ℓ} (hp : 2 < p)
    (hμ : IsPrimitiveRoot μ p) {k j : ℕ}
    (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k) (hjp : j < p) (hj0 : 0 < j)
    {w th : ZMod ℓ} (hth : th ≠ 0) (hw : w = -(μ ^ j * th))
    (heqs : ∀ a : ℕ, ¬ p ∣ a → ∃ g s₁ s₂ : ZMod ℓ, g ≠ 0 ∧
      w + μ ^ a * th = (1 - μ ^ a) * g * s₁ ^ p ∧
      w + μ ^ (a * (p - 1)) * th = (1 - μ ^ (a * (p - 1))) * g * s₂ ^ p) :
    ∀ c : ℕ, ¬ p ∣ c → ¬ p ∣ (c + 2 * j) →
      (1 - μ ^ (c + 2 * j)) ^ k = μ ^ (j * k) * (1 - μ ^ c) ^ k := by
  intro c hc hc2j
  have hkev : Even k := (even_iff_two_dvd).mpr hkeven
  by_cases hcenter : p ∣ (c + j)
  · -- direct identity: c ≡ −j, c+2j ≡ j
    obtain ⟨d, hd⟩ := hcenter
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at hd
      omega
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hpd : p * (d' + 1) = p * d' + p := by ring
    have hcmod : c % p = p - j := by
      have hceq : c = p * d' + (p - j) := by omega
      rw [hceq, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    have hc2jmod : (c + 2 * j) % p = j := by
      have h1 : c + 2 * j = p * (d' + 1) + j := by omega
      rw [h1, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [mu_pow_transport hμ (show (c + 2 * j) % p = j % p from by
        rw [hc2jmod, Nat.mod_eq_of_lt (show j < p from hjp)]),
      mu_pow_transport hμ (show c % p = (p - j) % p from by
        rw [hcmod, Nat.mod_eq_of_lt (show p - j < p from by omega)])]
    -- goal: (1 − μ^j)^k = μ^{jk}·(1 − μ^{p−j})^k
    have hmul : μ ^ (p - j) * μ ^ j = 1 := by
      rw [← pow_add, Nat.sub_add_cancel (le_of_lt hjp), hμ.pow_eq_one]
    have hkey : (1 - μ ^ (p - j)) = -(μ ^ (p - j)) * (1 - μ ^ j) := by
      linear_combination -hmul
    rw [hkey, mul_pow, hkev.neg_pow]
    have hμpk : μ ^ (j * k) * (μ ^ (p - j)) ^ k = 1 := by
      rw [← pow_mul, ← pow_add, show j * k + (p - j) * k = p * k from by
        rw [← Nat.add_mul, Nat.add_sub_cancel' (le_of_lt hjp)],
        pow_mul, hμ.pow_eq_one, one_pow]
    calc (1 - μ ^ j) ^ k
        = (μ ^ (j * k) * (μ ^ (p - j)) ^ k) * (1 - μ ^ j) ^ k := by rw [hμpk, one_mul]
      _ = μ ^ (j * k) * ((μ ^ (p - j)) ^ k * (1 - μ ^ j) ^ k) := by ring
  · -- the equations branch, at index a := c + j
    set a : ℕ := c + j with ha
    obtain ⟨g, s₁, s₂, hg, he₁, he₂⟩ := heqs a hcenter
    have hX₁ : w + μ ^ a * th = (μ ^ a - μ ^ j) * th := by
      rw [hw]
      ring
    have hX₂ : w + μ ^ (a * (p - 1)) * th = (μ ^ (a * (p - 1)) - μ ^ j) * th := by
      rw [hw]
      ring
    have hAinv : μ ^ a * μ ^ (a * (p - 1)) = 1 := by
      rw [← pow_add, show a + a * (p - 1) = a * p from by
        have h2 := hpri.out.two_le
        calc a + a * (p - 1) = a * (1 + (p - 1)) := by ring
          _ = a * p := by
            congr 1
            omega,
        mul_comm a p, pow_mul, hμ.pow_eq_one, one_pow]
    have hA1 : (1 : ZMod ℓ) - μ ^ a ≠ 0 := by
      intro h0
      exact hcenter ((hμ.pow_eq_one_iff_dvd a).mp (by linear_combination -h0))
    have hAJ : μ ^ a - μ ^ j ≠ 0 := by
      intro h0
      apply hc
      have heq : μ ^ a = μ ^ j := by linear_combination h0
      have h1 : μ ^ (a + (p - j)) = 1 := by
        rw [pow_add, heq, ← pow_add, Nat.add_sub_cancel' (le_of_lt hjp), hμ.pow_eq_one]
      have h2 := (hμ.pow_eq_one_iff_dvd _).mp h1
      rw [show a + (p - j) = c + p from by omega] at h2
      exact (Nat.dvd_add_self_right).mp h2
    have hAinvJ : μ ^ (a * (p - 1)) - μ ^ j ≠ 0 := by
      intro h0
      apply hc2j
      have heq : μ ^ (a * (p - 1)) = μ ^ j := by linear_combination h0
      have h1 : μ ^ (a + j) = 1 := by
        rw [pow_add, ← heq, hAinv]
      have h2 := (hμ.pow_eq_one_iff_dvd _).mp h1
      rwa [show a + j = c + 2 * j from by omega] at h2
    have hs₁ : s₁ ≠ 0 := by
      intro h0
      rw [h0, zero_pow hpri.out.ne_zero, mul_zero, hX₁] at he₁
      exact (mul_ne_zero hAJ hth) he₁
    have hs₂ : s₂ ≠ 0 := by
      intro h0
      rw [h0, zero_pow hpri.out.ne_zero, mul_zero, hX₂] at he₂
      exact (mul_ne_zero hAinvJ hth) he₂
    have hFerm : ∀ s : ZMod ℓ, s ≠ 0 → (s ^ p) ^ k = 1 := by
      intro s hs
      rw [← pow_mul, mul_comm p k, ← hℓk]
      exact ZMod.pow_card_sub_one_eq_one hs
    have hE₁ : (μ ^ a - μ ^ j) ^ k * th ^ k = (1 - μ ^ a) ^ k * g ^ k := by
      have h1 := congrArg (· ^ k) (hX₁.symm.trans he₁)
      simp only [mul_pow] at h1
      rw [hFerm s₁ hs₁, mul_one] at h1
      exact h1
    have hE₂ : (μ ^ (a * (p - 1)) - μ ^ j) ^ k * th ^ k
        = (1 - μ ^ (a * (p - 1))) ^ k * g ^ k := by
      have h1 := congrArg (· ^ k) (hX₂.symm.trans he₂)
      simp only [mul_pow] at h1
      rw [hFerm s₂ hs₂, mul_one] at h1
      exact h1
    have hthk : th ^ k ≠ 0 := pow_ne_zero _ hth
    have hkey : (μ ^ a - μ ^ j) ^ k * (1 - μ ^ (a * (p - 1))) ^ k
        = (μ ^ (a * (p - 1)) - μ ^ j) ^ k * (1 - μ ^ a) ^ k := by
      have h1 : ((μ ^ a - μ ^ j) ^ k * (1 - μ ^ (a * (p - 1))) ^ k) * th ^ k
          = ((μ ^ (a * (p - 1)) - μ ^ j) ^ k * (1 - μ ^ a) ^ k) * th ^ k := by
        calc ((μ ^ a - μ ^ j) ^ k * (1 - μ ^ (a * (p - 1))) ^ k) * th ^ k
            = ((μ ^ a - μ ^ j) ^ k * th ^ k) * (1 - μ ^ (a * (p - 1))) ^ k := by ring
          _ = ((1 - μ ^ a) ^ k * g ^ k) * (1 - μ ^ (a * (p - 1))) ^ k := by rw [hE₁]
          _ = ((1 - μ ^ (a * (p - 1))) ^ k * g ^ k) * (1 - μ ^ a) ^ k := by ring
          _ = ((μ ^ (a * (p - 1)) - μ ^ j) ^ k * th ^ k) * (1 - μ ^ a) ^ k := by rw [hE₂]
          _ = ((μ ^ (a * (p - 1)) - μ ^ j) ^ k * (1 - μ ^ a) ^ k) * th ^ k := by ring
      exact mul_right_cancel₀ hthk h1
    have h2 : μ ^ a * (1 - μ ^ (a * (p - 1))) = μ ^ a - 1 := by
      linear_combination -hAinv
    have h3 : μ ^ a * (μ ^ (a * (p - 1)) - μ ^ j) = 1 - μ ^ (a + j) := by
      rw [pow_add]
      linear_combination hAinv
    have hstep2 : (μ ^ a - μ ^ j) ^ k * (μ ^ a - 1) ^ k
        = (1 - μ ^ (a + j)) ^ k * (1 - μ ^ a) ^ k := by
      calc (μ ^ a - μ ^ j) ^ k * (μ ^ a - 1) ^ k
          = (μ ^ a - μ ^ j) ^ k * (μ ^ a * (1 - μ ^ (a * (p - 1)))) ^ k := by rw [h2]
        _ = ((μ ^ a - μ ^ j) ^ k * (1 - μ ^ (a * (p - 1))) ^ k) * (μ ^ a) ^ k := by
            rw [mul_pow]
            ring
        _ = ((μ ^ (a * (p - 1)) - μ ^ j) ^ k * (1 - μ ^ a) ^ k) * (μ ^ a) ^ k := by
            rw [hkey]
        _ = (μ ^ a * (μ ^ (a * (p - 1)) - μ ^ j)) ^ k * (1 - μ ^ a) ^ k := by
            rw [mul_pow]
            ring
        _ = (1 - μ ^ (a + j)) ^ k * (1 - μ ^ a) ^ k := by rw [h3]
    have hfin : (μ ^ a - μ ^ j) ^ k = (1 - μ ^ (a + j)) ^ k := by
      have h1 : (μ ^ a - μ ^ j) ^ k * (1 - μ ^ a) ^ k
          = (1 - μ ^ (a + j)) ^ k * (1 - μ ^ a) ^ k := by
        rw [← hstep2, show (μ ^ a - 1 : ZMod ℓ) = -(1 - μ ^ a) from by ring,
          hkev.neg_pow]
      exact mul_right_cancel₀ (pow_ne_zero k hA1) h1
    have h5 : (μ ^ a - μ ^ j) ^ k = μ ^ (j * k) * (1 - μ ^ c) ^ k := by
      have h6 : μ ^ a - μ ^ j = μ ^ j * -(1 - μ ^ c) := by
        rw [ha, pow_add]
        ring
      rw [h6, mul_pow, hkev.neg_pow, ← pow_mul]
    rw [show c + 2 * j = a + j from by omega, ← hfin, h5]

/-- **Layer 3a**: the real cyclotomic units die to the `k`: the ζ-power
normalization exactly cancels the telescoping drift. -/
theorem realCyc_pow_k_eq_one {K : Type*} [Field K] [CharZero K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) {k : ℕ}
    (hF : ∀ b : ℕ, ¬ p ∣ b →
      (1 - redRoot p ℓ t ^ b) ^ k
        = redRoot p ℓ t ^ (k * (b - 1) * ((p + 1) / 2)) * (1 - redRoot p ℓ t) ^ k)
    (a : ℕ) (ha1 : 1 ≤ a) (ha : a.Coprime p) :
    (redUnit hζ hμ (realCyclotomicUnit hζ a ha)) ^ k = 1 := by
  have hpa : ¬ p ∣ a := by
    intro hdvd
    have h1 : p ∣ Nat.gcd a p := Nat.dvd_gcd hdvd dvd_rfl
    rw [Nat.Coprime] at ha
    rw [ha] at h1
    have h2 := hpri.out.two_le
    exact absurd (Nat.le_of_dvd one_pos h1) (by omega)
  set Zu := redUnit hζ hμ (zetaUnit hζ) with hZu
  set Cu := redUnit hζ hμ
    (cyclotomicUnit hζ.toInteger_isPrimitiveRoot hpri.out.two_le ha) with hCu
  have hmap : redUnit hζ hμ (realCyclotomicUnit hζ a ha)
      = Zu ^ ((1 - (a : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ)) * Cu := by
    rw [realCyclotomicUnit, map_mul, map_zpow]
  have hμ1 : (1 : ZMod ℓ) - redRoot p ℓ t ≠ 0 := by
    intro h0
    exact (hμ.ne_one (by omega)) (by linear_combination -h0)
  have hCuk : Cu ^ k = Zu ^ (k * (a - 1) * ((p + 1) / 2)) := by
    have hcoeC : ((Cu : (ZMod ℓ)ˣ) : ZMod ℓ)
        = ∑ i ∈ Finset.range a, redRoot p ℓ t ^ i := by
      rw [hCu, coe_redUnit, redHom_cyclotomicUnit_val]
    have hcoeZ : ((Zu : (ZMod ℓ)ˣ) : ZMod ℓ) = redRoot p ℓ t := by
      rw [hZu, redUnit_zetaUnit_val]
    have hSum : (∑ i ∈ Finset.range a, redRoot p ℓ t ^ i) ^ k
        = redRoot p ℓ t ^ (k * (a - 1) * ((p + 1) / 2)) := by
      have hgeom : (1 - redRoot p ℓ t) * (∑ i ∈ Finset.range a, redRoot p ℓ t ^ i)
          = 1 - redRoot p ℓ t ^ a := by
        have h1 := geom_sum_mul (redRoot p ℓ t) a
        linear_combination -h1
      have h2 : (1 - redRoot p ℓ t) ^ k
            * (∑ i ∈ Finset.range a, redRoot p ℓ t ^ i) ^ k
          = (1 - redRoot p ℓ t) ^ k
            * redRoot p ℓ t ^ (k * (a - 1) * ((p + 1) / 2)) := by
        rw [← mul_pow, hgeom, hF a hpa]
        ring
      exact mul_left_cancel₀ (pow_ne_zero k hμ1) h2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hcoeC, hcoeZ, hSum]
  rw [hmap, mul_pow, hCuk, ← zpow_natCast
      (Zu ^ ((1 - (a : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ))) k, ← zpow_mul,
    ← zpow_natCast Zu (k * (a - 1) * ((p + 1) / 2)), ← zpow_add]
  rw [show (1 - (a : ℤ)) * (((p + 1) / 2 : ℕ) : ℤ) * (k : ℤ)
      + ((k * (a - 1) * ((p + 1) / 2) : ℕ) : ℤ) = 0 from by
    push_cast [Nat.cast_sub ha1]
    ring]
  exact zpow_zero Zu

/-- **Layer 3b**: the eigen units die to the `k`. -/
theorem eigen_pow_k_eq_one {K : Type*} [Field K] [CharZero K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) {k : ℕ}
    (hF : ∀ b : ℕ, ¬ p ∣ b →
      (1 - redRoot p ℓ t ^ b) ^ k
        = redRoot p ℓ t ^ (k * (b - 1) * ((p + 1) / 2)) * (1 - redRoot p ℓ t) ^ k)
    (i : ℕ) :
    redHom hζ hμ ((eigenCyclotomicUnit hζ i : (𝓞 K)ˣ) : 𝓞 K) ^ k = 1 := by
  have h1 : (redUnit hζ hμ (eigenCyclotomicUnit hζ i)) ^ k = 1 := by
    rw [eigenCyclotomicUnit, map_prod, ← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro x _
    rw [map_pow, ← pow_mul, mul_comm (x.1 ^ (p - 1 - i)) k, pow_mul,
      realCyc_pow_k_eq_one hζ hp hμ hF x.1 (Finset.mem_Icc.mp x.2).1
        (coprime_of_mem_Icc x.2), one_pow]
  have h2 := congrArg (Units.val) h1
  rwa [Units.val_pow_eq_pow_val, coe_redUnit, Units.val_one] at h2

/-- **Washington Lemma 9.8** (one-fixed-prime form): if `φ(ξ) = 0` for the
reduction hom `φ` of a certified auxiliary pair `(ℓ, t)`, then `φ(ω + θ) = 0`.
The descent data enters through the product decomposition and the paired
per-index equations; the `Q_{i₀}` certificate blocks every nonzero index. -/
theorem lemma_9_8_hom {K : Type*} [Field K] [CharZero K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (_hℓ : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    {i₀ : ℕ} (_hi₀ev : Even i₀) (_hi₀2 : 2 ≤ i₀) (_hi₀p : i₀ ≤ p - 3)
    (hQE : redHom hζ hμ (eigenCyclotomicUnit hζ i₀ : 𝓞 K) ^ ((ℓ - 1) / p) ≠ 1)
    {ω θ ξ W : 𝓞 K}
    (hprod : ∏ ζ' ∈ Polynomial.nthRootsFinset p (1 : 𝓞 K), (ω + ζ' * θ) = W * ξ ^ p)
    (_hW : redHom hζ hμ W ≠ 0)
    (hcop : ∃ r s : 𝓞 K, r * ω + s * θ = 1)
    (heqs : ∀ a : ℕ, ¬ p ∣ a → ∃ (ηa : (𝓞 K)ˣ) (ρa ρa' : 𝓞 K),
      ω + hζ.toInteger ^ a * θ
        = (1 - hζ.toInteger ^ a) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa ^ p ∧
      ω + hζ.toInteger ^ (a * (p - 1)) * θ
        = (1 - hζ.toInteger ^ (a * (p - 1))) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa' ^ p)
    (hφξ : redHom hζ hμ ξ = 0) :
    redHom hζ hμ (ω + θ) = 0 := by
  classical
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hφζ : redHom hζ hμ hζ.toInteger = redRoot p ℓ t := redHom_zeta hζ hμ
  have hφprod : ∏ ζ' ∈ Polynomial.nthRootsFinset p (1 : 𝓞 K),
      redHom hζ hμ (ω + ζ' * θ) = 0 := by
    rw [← map_prod, hprod, map_mul, map_pow, hφξ,
      zero_pow hpri.out.ne_zero, mul_zero]
  obtain ⟨ζ', hζ'mem, hζ'0⟩ := Finset.prod_eq_zero_iff.mp hφprod
  have hζ'pow : ζ' ^ p = 1 :=
    (Polynomial.mem_nthRootsFinset hpri.out.pos _).mp hζ'mem
  obtain ⟨j, hjlt, hjeq⟩ :=
    hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hζ'pow
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [pow_zero] at hjeq
    rw [← hjeq, one_mul] at hζ'0
    exact hζ'0
  · exfalso
    have hφfac : redHom hζ hμ ω + redRoot p ℓ t ^ j * redHom hζ hμ θ = 0 := by
      have h1 := hζ'0
      rw [← hjeq, map_add, map_mul, map_pow, hφζ] at h1
      exact h1
    have hφθ : redHom hζ hμ θ ≠ 0 := by
      intro h0
      have hφω : redHom hζ hμ ω = 0 := by
        rw [h0, mul_zero, add_zero] at hφfac
        exact hφfac
      obtain ⟨r, s, hrs⟩ := hcop
      have h1 := congrArg (redHom hζ hμ) hrs
      rw [map_add, map_mul, map_mul, hφω, h0, mul_zero, mul_zero, add_zero,
        map_one] at h1
      exact zero_ne_one h1
    have hw : redHom hζ hμ ω = -(redRoot p ℓ t ^ j * redHom hζ hμ θ) := by
      linear_combination hφfac
    have heqs' : ∀ a : ℕ, ¬ p ∣ a → ∃ g s₁ s₂ : ZMod ℓ, g ≠ 0 ∧
        redHom hζ hμ ω + redRoot p ℓ t ^ a * redHom hζ hμ θ
          = (1 - redRoot p ℓ t ^ a) * g * s₁ ^ p ∧
        redHom hζ hμ ω + redRoot p ℓ t ^ (a * (p - 1)) * redHom hζ hμ θ
          = (1 - redRoot p ℓ t ^ (a * (p - 1))) * g * s₂ ^ p := by
      intro a ha
      obtain ⟨ηa, ρa, ρa', he₁, he₂⟩ := heqs a ha
      refine ⟨redHom hζ hμ ((ηa : (𝓞 K)ˣ) : 𝓞 K), redHom hζ hμ ρa,
        redHom hζ hμ ρa', ?_, ?_, ?_⟩
      · intro h0
        have h1 : redHom hζ hμ ((ηa : (𝓞 K)ˣ) : 𝓞 K)
            * redHom hζ hμ (((ηa⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) = 1 := by
          rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      · have h1 := congrArg (redHom hζ hμ) he₁
        rw [map_add, map_mul, map_pow, hφζ, map_mul, map_mul, map_sub, map_one,
          map_pow, map_pow, hφζ] at h1
        exact h1
      · have h1 := congrArg (redHom hζ hμ) he₂
        rw [map_add, map_mul, map_pow, hφζ, map_mul, map_mul, map_sub, map_one,
          map_pow, map_pow, hφζ] at h1
        exact h1
    have hrec := hrec_of_equations hp hμ hℓk hkeven hjlt hj0 hφθ hw heqs'
    have hF := telescope_main hpri.out hp hμ hjlt hj0 hrec
    have hkval : (ℓ - 1) / p = k := by
      rw [hℓk]
      exact Nat.mul_div_cancel k hpri.out.pos
    exact hQE (by rw [hkval]; exact eigen_pow_k_eq_one hζ hp hμ hF i₀)

/-- **Washington Lemma 9.8** at the base prime, certificate in `Q_i` form. -/
theorem lemma_9_8 {K : Type*} [Field K] [CharZero K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hℓ : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    {i₀ : ℕ} (hi₀ev : Even i₀) (hi₀2 : 2 ≤ i₀) (hi₀p : i₀ ≤ p - 3)
    (hQi : qi p i₀ ℓ t ^ ((ℓ - 1) / p) ≠ 1)
    {ω θ ξ W : 𝓞 K}
    (hprod : ∏ ζ' ∈ Polynomial.nthRootsFinset p (1 : 𝓞 K), (ω + ζ' * θ) = W * ξ ^ p)
    (hW : redHom hζ hμ W ≠ 0)
    (hcop : ∃ r s : 𝓞 K, r * ω + s * θ = 1)
    (heqs : ∀ a : ℕ, ¬ p ∣ a → ∃ (ηa : (𝓞 K)ˣ) (ρa ρa' : 𝓞 K),
      ω + hζ.toInteger ^ a * θ
        = (1 - hζ.toInteger ^ a) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa ^ p ∧
      ω + hζ.toInteger ^ (a * (p - 1)) * θ
        = (1 - hζ.toInteger ^ (a * (p - 1))) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa' ^ p)
    (hφξ : redHom hζ hμ ξ = 0) :
    redHom hζ hμ (ω + θ) = 0 := by
  have hkval : (ℓ - 1) / p = k := by
    rw [hℓk]
    exact Nat.mul_div_cancel k hpri.out.pos
  refine lemma_9_8_hom hζ hp hℓ hμ hℓk hkeven hi₀ev hi₀2 hi₀p ?_ hprod hW hcop
    heqs hφξ
  rw [redHom_eigen_pow_eq_Qi_pow (hζ := hζ) (hμ := hμ) (i := i₀) (hp := by omega)
    (hℓ := hℓ) (hkeven := by rw [hkval]; exact hkeven) (hieven := hi₀ev)
    (hi2 := hi₀2) (hip := hi₀p)]
  exact hQi

end Assembly

/-! ### Lemma 9.9, combinatorial layer: orthogonality kill and p-torsion dlog -/

section Chars

variable {p : ℕ} [hp' : Fact p.Prime]

/-- **Orthogonality kill** (the formal Vandermonde): if
`∑_i f i·α^{c i} = 0` for every unit `α` of `ZMod p` and the exponents `c i`
are distinct mod `p − 1`, then every coefficient vanishes. This is what turns
the per-conjugate-prime relations of Lemma 9.9 into `p ∣ d_i` at each index. -/
theorem vandermonde_kill (hp : 2 < p) {s : Finset ℕ} {f : ℕ → ZMod p} {c : ℕ → ℕ}
    (hcinj : ∀ i ∈ s, ∀ i' ∈ s, c i % (p - 1) = c i' % (p - 1) → i = i')
    (hrel : ∀ α : (ZMod p)ˣ, ∑ i ∈ s, f i * ((α : ZMod p)) ^ (c i) = 0) :
    ∀ i₀ ∈ s, f i₀ = 0 := by
  intro i₀ hi₀
  classical
  set r₀ : ℕ := c i₀ % (p - 1) with hr₀
  have hr₀lt : r₀ < p - 1 := Nat.mod_lt _ (by omega)
  set c' : ℕ := (p - 1) - r₀ with hc'
  have hsum2 : ∑ α : (ZMod p)ˣ, ∑ i ∈ s, f i * ((α : ZMod p)) ^ (c i + c') = 0 := by
    calc ∑ α : (ZMod p)ˣ, ∑ i ∈ s, f i * ((α : ZMod p)) ^ (c i + c')
        = ∑ α : (ZMod p)ˣ, (∑ i ∈ s, f i * ((α : ZMod p)) ^ (c i))
            * ((α : ZMod p)) ^ c' := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [pow_add]
          ring
      _ = 0 := Finset.sum_eq_zero fun α _ => by rw [hrel α, zero_mul]
  rw [Finset.sum_comm] at hsum2
  have hiff : ∀ i ∈ s, ((p - 1) ∣ (c i + c') ↔ i = i₀) := by
    intro i hi
    have hpm : 0 < p - 1 := by omega
    constructor
    · intro hdvd
      apply hcinj i hi i₀ hi₀
      have h1 : (c i + c') % (p - 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
      have h3 : (c i + c') % (p - 1) = (c i % (p - 1) + c') % (p - 1) := by
        conv_lhs => rw [← Nat.div_add_mod (c i) (p - 1)]
        rw [Nat.add_assoc, Nat.mul_add_mod]
      rw [h3] at h1
      have hrlt : c i % (p - 1) < p - 1 := Nat.mod_lt _ hpm
      have h4 : c i % (p - 1) + c' = p - 1 := by
        rcases Nat.lt_or_ge (c i % (p - 1) + c') (p - 1) with h5 | h5
        · rw [Nat.mod_eq_of_lt h5] at h1
          omega
        · have h6 : c i % (p - 1) + c' - (p - 1) < p - 1 := by omega
          rw [Nat.mod_eq_sub_mod h5, Nat.mod_eq_of_lt h6] at h1
          omega
      omega
    · rintro rfl
      refine ⟨c i / (p - 1) + 1, ?_⟩
      have h1 := Nat.div_add_mod (c i) (p - 1)
      have h2 : (p - 1) * (c i / (p - 1) + 1)
          = (p - 1) * (c i / (p - 1)) + (p - 1) := by ring
      omega
  have hpoint : ∀ i ∈ s, (∑ α : (ZMod p)ˣ, f i * ((α : ZMod p)) ^ (c i + c'))
      = f i * (if i = i₀ then (-1 : ZMod p) else 0) := by
    intro i hi
    rw [← Finset.mul_sum]
    congr 1
    have h1 := FiniteField.sum_pow_units (ZMod p) (c i + c')
    rw [ZMod.card] at h1
    rw [h1]
    by_cases hdd : (p - 1) ∣ (c i + c')
    · rw [if_pos hdd, if_pos ((hiff i hi).mp hdd)]
    · rw [if_neg hdd, if_neg (fun h => hdd ((hiff i hi).mpr h))]
  have hfin : ∑ i ∈ s, f i * (if i = i₀ then (-1 : ZMod p) else 0) = 0 := by
    calc ∑ i ∈ s, f i * (if i = i₀ then (-1 : ZMod p) else 0)
        = ∑ i ∈ s, ∑ α : (ZMod p)ˣ, f i * ((α : ZMod p)) ^ (c i + c') :=
          (Finset.sum_congr rfl hpoint).symm
      _ = 0 := hsum2
  rw [Finset.sum_eq_single i₀ (fun i _ hne => by rw [if_neg hne, mul_zero])
    (fun h => absurd hi₀ h), if_pos rfl] at hfin
  linear_combination -hfin

end Chars

/-! ### p-torsion discrete logarithm -/

section Dlog

variable {F : Type*} [Field F] {p : ℕ} {μ : F}

theorem exists_dlog [NeZero p] (hμ : IsPrimitiveRoot μ p) {x : F} (hx : x ^ p = 1) :
    ∃ e : ZMod p, μ ^ e.val = x := by
  obtain ⟨i, hilt, hieq⟩ := hμ.eq_pow_of_pow_eq_one hx
  exact ⟨(i : ZMod p), by rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hilt]⟩

theorem dlog_unique [NeZero p] (hμ : IsPrimitiveRoot μ p) {e e' : ZMod p}
    (h : μ ^ e.val = μ ^ e'.val) : e = e' := by
  have h1 := hμ.pow_inj (ZMod.val_lt e) (ZMod.val_lt e') h
  exact ZMod.val_injective p h1

open scoped Classical in
/-- The discrete log of a `p`-torsion element, base `μ` (junk value `0` off
the torsion). -/
noncomputable def pDlog [NeZero p] (hμ : IsPrimitiveRoot μ p) (x : F) : ZMod p :=
  if hx : x ^ p = 1 then (exists_dlog hμ hx).choose else 0

theorem pDlog_spec [NeZero p] (hμ : IsPrimitiveRoot μ p) {x : F} (hx : x ^ p = 1) :
    μ ^ (pDlog hμ x).val = x := by
  rw [pDlog, dif_pos hx]
  exact (exists_dlog hμ hx).choose_spec

theorem pDlog_one [NeZero p] (hμ : IsPrimitiveRoot μ p) : pDlog hμ (1 : F) = 0 := by
  apply dlog_unique hμ
  rw [pDlog_spec hμ (one_pow p), ZMod.val_zero, pow_zero]

theorem pDlog_mul [NeZero p] (hμ : IsPrimitiveRoot μ p) {x y : F}
    (hx : x ^ p = 1) (hy : y ^ p = 1) :
    pDlog hμ (x * y) = pDlog hμ x + pDlog hμ y := by
  have hxy : (x * y) ^ p = 1 := by rw [mul_pow, hx, hy, one_mul]
  apply dlog_unique hμ
  rw [pDlog_spec hμ hxy,
    show μ ^ ((pDlog hμ x + pDlog hμ y).val)
      = μ ^ ((pDlog hμ x).val + (pDlog hμ y).val) from
      mu_pow_transport hμ (by
        rw [Nat.mod_eq_of_lt (ZMod.val_lt _), ZMod.val_add]),
    pow_add, pDlog_spec hμ hx, pDlog_spec hμ hy]

theorem pow_p_torsion {x : F} (hx : x ^ p = 1) (m : ℕ) : (x ^ m) ^ p = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]

theorem pDlog_pow [NeZero p] (hμ : IsPrimitiveRoot μ p) {x : F}
    (hx : x ^ p = 1) (m : ℕ) :
    pDlog hμ (x ^ m) = m * pDlog hμ x := by
  induction m with
  | zero => rw [pow_zero, pDlog_one hμ, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [pow_succ, pDlog_mul hμ (pow_p_torsion hx n) hx, ih]
    push_cast
    ring

/-- `pDlog x = 0` forces `x = 1` on the torsion — the certificate direction. -/
theorem pDlog_eq_zero_iff [NeZero p] (hμ : IsPrimitiveRoot μ p) {x : F}
    (hx : x ^ p = 1) : pDlog hμ x = 0 ↔ x = 1 := by
  constructor
  · intro h0
    have h1 := pDlog_spec hμ hx
    rw [h0, ZMod.val_zero, pow_zero] at h1
    exact h1.symm
  · rintro rfl
    exact pDlog_one hμ

theorem pDlog_prod [NeZero p] (hμ : IsPrimitiveRoot μ p) {ι : Type*}
    (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ^ p = 1) :
    pDlog hμ (∏ i ∈ s, f i) = ∑ i ∈ s, pDlog hμ (f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [pDlog_one hμ]
  · intro i s his ih hf
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ^ p = 1 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ s, f j) ^ p = 1 := by
      rw [← Finset.prod_pow]
      exact Finset.prod_eq_one hfs
    rw [Finset.prod_insert his, pDlog_mul hμ hfi hprod, ih hfs,
      Finset.sum_insert his]

end Dlog

/-! ### CRT layer: the joint kernel of the reduction homs is (ℓ) -/

section CRT

variable {p : ℕ} [hpri : Fact p.Prime] {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime]
variable {K : Type*} [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

open FltVandiver
open scoped NumberField

omit [NumberField K] in
/-- Forward direction: `ℓ ∣ x` kills every reduction hom. -/
theorem redHom_eq_zero_of_dvd (hζ : IsPrimitiveRoot ζ p)
    (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) {x : 𝓞 K}
    (hdvd : ((ℓ : ℕ) : 𝓞 K) ∣ x) : redHom hζ hμ x = 0 := by
  obtain ⟨y, rfl⟩ := hdvd
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

omit [NumberField K] in
/-- **CRT, joint-kernel direction**: an integer of `K` killed by the reduction
hom at every primitive `p`-th root of `ZMod ℓ` is divisible by `ℓ`. Proof: in
the integral power basis, the reduced coordinate polynomial has degree
`< p − 1` and vanishes at all `p − 1` primitive roots, hence is zero. -/
theorem dvd_of_forall_redHom_eq_zero (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) {x : 𝓞 K}
    (h : ∀ (t' : ℕ) (hμ' : IsPrimitiveRoot (redRoot p ℓ t') p),
      redHom hζ hμ' x = 0) :
    ((ℓ : ℕ) : 𝓞 K) ∣ x := by
  classical
  obtain ⟨f, hdeg, hx⟩ := hζ.integralPowerBasis.exists_eq_aeval x
  rw [hζ.integralPowerBasis_dim, Nat.totient_prime hpri.out] at hdeg
  set g : Polynomial (ZMod ℓ) := f.map (Int.castRingHom (ZMod ℓ)) with hg
  have hgdeg : g.natDegree < p - 1 :=
    lt_of_le_of_lt (Polynomial.natDegree_map_le) hdeg
  have hgzero : g = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g
      (primitiveRoots p (ZMod ℓ))
    · intro ν hν
      have hνprim : IsPrimitiveRoot ν p := (mem_primitiveRoots (by omega)).mp hν
      obtain ⟨α, hαlt, hαeq⟩ := hμ.eq_pow_of_pow_eq_one hνprim.pow_eq_one
      have hredα : redRoot p ℓ (t ^ α) = ν := by
        rw [← hαeq, redRoot, redRoot]
        push_cast
        rw [← pow_mul, mul_comm α ((ℓ - 1) / p), pow_mul]
      have hμ' : IsPrimitiveRoot (redRoot p ℓ (t ^ α)) p := by
        rw [hredα]
        exact hνprim
      calc g.eval ν = Polynomial.aeval ν f := by
            rw [hg, Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]
        _ = Polynomial.aeval (redRoot p ℓ (t ^ α)) f := by rw [hredα]
        _ = redHom hζ hμ' (Polynomial.aeval hζ.integralPowerBasis.gen f) := by
            rw [show redRoot p ℓ (t ^ α)
                = redHom hζ hμ' hζ.integralPowerBasis.gen from by
              rw [hζ.integralPowerBasis_gen]
              exact (redHom_zeta hζ hμ').symm,
              Polynomial.aeval_algHom_apply]
        _ = 0 := by
            rw [← hx]
            exact h (t ^ α) hμ'
    · have hcard : (primitiveRoots p (ZMod ℓ)).card = p.totient :=
        hμ.card_primitiveRoots
      rw [hcard, Nat.totient_prime hpri.out]
      exact hgdeg
  have hcoeff : ∀ i, ((ℓ : ℕ) : ℤ) ∣ f.coeff i := by
    intro i
    have h1 : ((f.coeff i : ℤ) : ZMod ℓ) = 0 := by
      have h2 := congrArg (fun q => Polynomial.coeff q i) hgzero
      simpa [hg, Polynomial.coeff_map] using h2
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h1
    exact_mod_cast h3
  have hCdvd : Polynomial.C ((ℓ : ℕ) : ℤ) ∣ f :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hcoeff
  obtain ⟨f', hf'⟩ := hCdvd
  refine ⟨Polynomial.aeval hζ.integralPowerBasis.gen f', ?_⟩
  rw [hx, hf', map_mul, Polynomial.aeval_C, algebraMap_int_eq]
  congr 1
  simp

end CRT

/-! ### Equivariance layer: certificates propagate to conjugate reduction homs

The `p − 1` primes above `ℓ` correspond to the reduction homs at the conjugate
roots `μ^α`.  Composing with the Galois action (`redHom_conj`) and extracting
the multiplicative form of `galV_eigen` (`galUnit_eigen_decomp`) shows the
single certificate `Q_i^k ≠ 1` at `(ℓ, t)` blocks the eigen unit at EVERY
conjugate, twisted by `α^i` — exactly the coefficient shape `vandermonde_kill`
consumes. -/

section Equivariance

open CyclotomicNT FltVandiver FltVandiver.QiCert NumberField NumberField.IsCMField
open scoped NumberField

variable {p : ℕ} [hpri : Fact p.Prime] {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime]
variable {K : Type*} [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

omit hpri in
/-- Conjugating the seed `t ↦ t^a` raises the reduction root to the `a`-th
power. -/
theorem redRoot_pow (a : ℕ) : redRoot p ℓ (t ^ a) = redRoot p ℓ t ^ a := by
  rw [redRoot, redRoot, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm]

/-- The conjugate seeds `t^{g.val}` are again admissible. -/
theorem isPrimitiveRoot_redRoot_pow (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    (g : (ZMod p)ˣ) :
    IsPrimitiveRoot (redRoot p ℓ (t ^ (g : ZMod p).val)) p := by
  rw [redRoot_pow]
  exact hμ.pow_of_coprime _ (coprime_val g)

omit [NumberField K] in
/-- The integral Galois action sends `ζ` (as an algebraic integer) to
`ζ^{g.val}`. -/
theorem mapRingEquiv_galAut_toInteger (hζ : IsPrimitiveRoot ζ p) (g : (ZMod p)ˣ) :
    RingOfIntegers.mapRingEquiv (galAut hζ g).toRingEquiv hζ.toInteger
      = hζ.toInteger ^ (g : ZMod p).val := by
  apply RingOfIntegers.coe_injective
  have hL : (algebraMap (𝓞 K) K)
      (RingOfIntegers.mapRingEquiv (galAut hζ g).toRingEquiv hζ.toInteger)
      = galAut hζ g ζ := rfl
  have hB : (algebraMap (𝓞 K) K) hζ.toInteger = ζ := rfl
  rw [hL, map_pow, hB, galAut_zeta]

omit [NumberField K] in
/-- **Conjugate reduction homs**: the hom at the conjugate seed `t^{g.val}` is
the hom at `t` composed with the Galois action `σ_g`. -/
theorem redHom_conj (hζ : IsPrimitiveRoot ζ p)
    (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) (g : (ZMod p)ˣ)
    (hμ' : IsPrimitiveRoot (redRoot p ℓ (t ^ (g : ZMod p).val)) p) (x : 𝓞 K) :
    redHom hζ hμ' x
      = redHom hζ hμ (RingOfIntegers.mapRingEquiv (galAut hζ g).toRingEquiv x) := by
  have hext : redHom hζ hμ'
      = (redHom hζ hμ).comp
          (RingOfIntegers.mapRingEquiv (galAut hζ g).toRingEquiv).toRingHom.toIntAlgHom := by
    apply hζ.integralPowerBasis.algHom_ext
    rw [hζ.integralPowerBasis_gen]
    change redHom hζ hμ' hζ.toInteger
        = redHom hζ hμ (RingOfIntegers.mapRingEquiv (galAut hζ g).toRingEquiv hζ.toInteger)
    rw [redHom_zeta, mapRingEquiv_galAut_toInteger hζ g, map_pow, redHom_zeta,
      redRoot_pow]
  rw [hext]
  rfl

/-- **Multiplicative form of `galV_eigen`**: the Galois conjugate of the eigen
unit is its `g^i`-th power times a `p`-th power of a unit. -/
theorem galUnit_eigen_decomp [NumberField.IsCMField K]
    (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2) (g : (ZMod p)ˣ)
    (i : ℕ) (hi : Even i) (h2 : 2 ≤ i) (h3 : i ≤ p - 3) :
    ∃ v : (𝓞 K)ˣ, galUnit hζ g (eigenCyclotomicUnit hζ i)
      = eigenCyclotomicUnit hζ i ^ ((g : ZMod p) ^ i).val * v ^ p := by
  set Ei : realUnits K :=
    ⟨eigenCyclotomicUnit hζ i, eigenCyclotomicUnit_mem_realUnits hζ hp i⟩ with hEi
  set n : ℕ := ((g : ZMod p) ^ i).val with hn
  have h1 : (vOf (galUnitReal hζ g Ei) : ModN (Additive (realUnits K)) p)
      = ((g : ZMod p) ^ i) • (vOf Ei : ModN (Additive (realUnits K)) p) := by
    rw [← galV_vOf]
    exact galV_eigen hζ hp g i hi h2 h3
  have h2' : (vOf (Ei ^ n) : ModN (Additive (realUnits K)) p)
      = ((g : ZMod p) ^ i) • vOf Ei := by
    rw [vOf_pow, ← Nat.cast_smul_eq_nsmul (ZMod p)]
    congr 1
    rw [hn, ZMod.natCast_zmod_val]
  have h3' : (vOf (galUnitReal hζ g Ei * (Ei ^ n)⁻¹) :
      ModN (Additive (realUnits K)) p) = 0 := by
    rw [vOf_mul, vOf_inv, h1, h2', add_neg_cancel]
  obtain ⟨v, hv⟩ := (vOf_eq_zero_iff _).mp h3'
  refine ⟨(v : (𝓞 K)ˣ), ?_⟩
  have hu : galUnitReal hζ g Ei = Ei ^ n * v ^ p := by
    rw [mul_comm]
    exact (mul_inv_eq_iff_eq_mul.mp hv)
  exact congrArg (fun u : realUnits K => (u : (𝓞 K)ˣ)) hu

/-- The certificate value at the conjugate hom is the `((g^i).val)`-th power of
the base certificate value: `φ_{t^g}(E_i)^k = (Q_i^k)^{g^i}`. -/
theorem redHom_conj_eigen_pow [NumberField.IsCMField K]
    (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2)
    (hℓ : ℓ % p = 1) (hkeven : 2 ∣ (ℓ - 1) / p)
    (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) (g : (ZMod p)ˣ)
    (hμ' : IsPrimitiveRoot (redRoot p ℓ (t ^ (g : ZMod p).val)) p)
    (i : ℕ) (hi : Even i) (h2 : 2 ≤ i) (h3 : i ≤ p - 3) :
    redHom hζ hμ' (eigenCyclotomicUnit hζ i : 𝓞 K) ^ ((ℓ - 1) / p)
      = (qi p i ℓ t ^ ((ℓ - 1) / p)) ^ ((g : ZMod p) ^ i).val := by
  set k := (ℓ - 1) / p with hk
  set n : ℕ := ((g : ZMod p) ^ i).val with hn
  have hdvd : p ∣ ℓ - 1 := by
    have h := Nat.div_add_mod ℓ p
    exact ⟨ℓ / p, by omega⟩
  have hpk : p * k = ℓ - 1 := by
    rw [hk]
    exact Nat.mul_div_cancel' hdvd
  obtain ⟨v, hv⟩ := galUnit_eigen_decomp hζ hp g i hi h2 h3
  have hvv := congrArg (Units.val) hv
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hvv
  have hcoe : RingOfIntegers.mapRingEquiv (galAut hζ g).toRingEquiv
      (eigenCyclotomicUnit hζ i : 𝓞 K)
      = ((galUnit hζ g (eigenCyclotomicUnit hζ i) : (𝓞 K)ˣ) : 𝓞 K) := rfl
  rw [redHom_conj hζ hμ g hμ', hcoe, hvv, map_mul, map_pow, map_pow, mul_pow,
    ← pow_mul, ← pow_mul]
  have hunit : redHom hζ hμ ((v : (𝓞 K)ˣ) : 𝓞 K) ≠ 0 :=
    ((v : (𝓞 K)ˣ).isUnit.map (redHom hζ hμ)).ne_zero
  rw [show p * k = ℓ - 1 from hpk, ZMod.pow_card_sub_one_eq_one hunit, mul_one,
    mul_comm n k, pow_mul, hk,
    redHom_eigen_pow_eq_Qi_pow (hζ := hζ) (hμ := hμ) (i := i) (hp := hp)
      (hℓ := hℓ) (hkeven := hkeven) (hieven := hi) (hi2 := h2) (hip := h3)]

/-- **Certificates at conjugates**: the single certificate `Q_i^k ≠ 1` at
`(ℓ, t)` blocks the eigen unit at every conjugate reduction hom. -/
theorem cert_at_conj [NumberField.IsCMField K]
    (hζ : IsPrimitiveRoot ζ p) (hp : p ≠ 2)
    (hℓ : ℓ % p = 1) (hkeven : 2 ∣ (ℓ - 1) / p)
    (hμ : IsPrimitiveRoot (redRoot p ℓ t) p) (g : (ZMod p)ˣ)
    (hμ' : IsPrimitiveRoot (redRoot p ℓ (t ^ (g : ZMod p).val)) p)
    (i : ℕ) (hi : Even i) (h2 : 2 ≤ i) (h3 : i ≤ p - 3)
    (hQi : qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1) :
    redHom hζ hμ' (eigenCyclotomicUnit hζ i : 𝓞 K) ^ ((ℓ - 1) / p) ≠ 1 := by
  rw [redHom_conj_eigen_pow hζ hp hℓ hkeven hμ g hμ' i hi h2 h3]
  set Q := qi p i ℓ t ^ ((ℓ - 1) / p) with hQ
  have hdvd : p ∣ ℓ - 1 := by
    have h := Nat.div_add_mod ℓ p
    exact ⟨ℓ / p, by omega⟩
  have hpk : (ℓ - 1) / p * p = ℓ - 1 := Nat.div_mul_cancel hdvd
  have hE0 : redHom hζ hμ (eigenCyclotomicUnit hζ i : 𝓞 K) ≠ 0 :=
    ((eigenCyclotomicUnit hζ i).isUnit.map (redHom hζ hμ)).ne_zero
  have hQp : Q ^ p = 1 := by
    rw [hQ, ← redHom_eigen_pow_eq_Qi_pow (hζ := hζ) (hμ := hμ) (i := i) (hp := hp)
        (hℓ := hℓ) (hkeven := hkeven) (hieven := hi) (hi2 := h2) (hip := h3),
      ← pow_mul, hpk,
      ZMod.pow_card_sub_one_eq_one hE0]
  have hordQ : orderOf Q = p := by
    rcases hpri.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hQp) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hQi
    · exact h1
  intro hcon
  have hdvd2 := orderOf_dvd_of_pow_eq_one hcon
  rw [hordQ] at hdvd2
  have hne : ((g : ZMod p) ^ i) ≠ 0 := by
    rw [← Units.val_pow_eq_pow_val]
    exact Units.ne_zero _
  have hne' : ((g : ZMod p) ^ i).val ≠ 0 := fun h0 => hne (by rwa [← ZMod.val_eq_zero])
  have hlt : ((g : ZMod p) ^ i).val < p := ZMod.val_lt _
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne') hdvd2) (by omega)

omit [NumberField K] in
/-- The reduction hom depends only on the value of the reduction root. -/
theorem redHom_congr {t₁ t₂ : ℕ} (hζ : IsPrimitiveRoot ζ p)
    (hμ₁ : IsPrimitiveRoot (redRoot p ℓ t₁) p)
    (hμ₂ : IsPrimitiveRoot (redRoot p ℓ t₂) p)
    (h : redRoot p ℓ t₁ = redRoot p ℓ t₂) :
    redHom hζ hμ₁ = redHom hζ hμ₂ := by
  apply hζ.integralPowerBasis.algHom_ext
  rw [hζ.integralPowerBasis_gen, redHom_zeta, redHom_zeta, h]

/-- Every admissible seed is a conjugate of the base seed: its reduction root
is `μ^{g.val}` for some unit `g` of `ZMod p`. -/
theorem exists_conj_seed (hp : 2 < p) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {t' : ℕ} (hμ' : IsPrimitiveRoot (redRoot p ℓ t') p) :
    ∃ g : (ZMod p)ˣ, redRoot p ℓ t' = redRoot p ℓ (t ^ (g : ZMod p).val) := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  obtain ⟨j, hjlt, hjeq⟩ := hμ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hjeq
    exact hμ'.ne_one (by omega) hjeq.symm
  have hpj : ¬ p ∣ j := fun hdvd =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hdvd) (by omega)
  have hcop : j.Coprime p :=
    Nat.coprime_comm.mp ((hpri.out.coprime_iff_not_dvd).mpr hpj)
  refine ⟨ZMod.unitOfCoprime j hcop, ?_⟩
  have hval : ((ZMod.unitOfCoprime j hcop : ZMod p)).val = j := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hjlt]
  rw [redRoot_pow, hval]
  exact hjeq.symm

/-- **Washington Lemma 9.8, full-invariant form**: the certificate at the
single pair `(ℓ, t)` plus the descent data upgrade `ℓ ∣ ξ` to `ℓ ∣ ω + θ`.
The proof runs `lemma_9_8_hom` at every conjugate reduction hom — the
certificate transports by `cert_at_conj` — and reassembles by CRT. -/
theorem lemma_9_8_all [NumberField.IsCMField K]
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hℓ : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    {i₀ : ℕ} (hi₀ev : Even i₀) (hi₀2 : 2 ≤ i₀) (hi₀p : i₀ ≤ p - 3)
    (hQi : qi p i₀ ℓ t ^ ((ℓ - 1) / p) ≠ 1)
    {ω θ ξ W : 𝓞 K}
    (hprod : ∏ ζ' ∈ Polynomial.nthRootsFinset p (1 : 𝓞 K), (ω + ζ' * θ) = W * ξ ^ p)
    (hW : ∀ (t' : ℕ) (hμ' : IsPrimitiveRoot (redRoot p ℓ t') p),
      redHom hζ hμ' W ≠ 0)
    (hcop : ∃ r s : 𝓞 K, r * ω + s * θ = 1)
    (heqs : ∀ a : ℕ, ¬ p ∣ a → ∃ (ηa : (𝓞 K)ˣ) (ρa ρa' : 𝓞 K),
      ω + hζ.toInteger ^ a * θ
        = (1 - hζ.toInteger ^ a) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa ^ p ∧
      ω + hζ.toInteger ^ (a * (p - 1)) * θ
        = (1 - hζ.toInteger ^ (a * (p - 1))) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa' ^ p)
    (hξ : ((ℓ : ℕ) : 𝓞 K) ∣ ξ) :
    ((ℓ : ℕ) : 𝓞 K) ∣ (ω + θ) := by
  have hkval : (ℓ - 1) / p = k := by
    rw [hℓk]
    exact Nat.mul_div_cancel k hpri.out.pos
  apply dvd_of_forall_redHom_eq_zero hζ hp hμ
  intro t' hμ'
  obtain ⟨g, hg⟩ := exists_conj_seed hp hμ hμ'
  have hμ'' : IsPrimitiveRoot (redRoot p ℓ (t ^ (g : ZMod p).val)) p := hg ▸ hμ'
  rw [redHom_congr hζ hμ' hμ'' hg]
  exact lemma_9_8_hom hζ hp hℓ hμ'' hℓk hkeven hi₀ev hi₀2 hi₀p
    (cert_at_conj hζ (by omega) hℓ (by rw [hkval]; exact hkeven) hμ g hμ'' i₀
      hi₀ev hi₀2 hi₀p hQi)
    hprod (hW _ hμ'') hcop heqs (redHom_eq_zero_of_dvd hζ hμ'' hξ)

end Equivariance

/-! ### Lemma 9.9: the eigenspace join

With `ℓ ∣ ω + θ` (the output of `lemma_9_8_all`), every reduced paired
equation collapses to `φ(η_a)·φ(ρ_a)^p = −φ(θ)`, so `φ(η_a/η_b)^k = 1` at
every reduction hom — no telescoping needed (`eta_pow_k_eq`).  `lemma_9_9`
then upgrades this to a GLOBAL `p`-th power: the all-even-index certificate
gives both the eigen span (via `prop_8_18` + `eigenFamily_span`) and, through
`cert_at_conj` and the `pDlog`/`vandermonde_kill` layer, the vanishing of
every eigen exponent. -/

section Join

open CyclotomicNT FltVandiver FltVandiver.QiCert NumberField NumberField.IsCMField
open scoped NumberField

variable {p : ℕ} [hpri : Fact p.Prime] {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime]
variable {K : Type*} [Field K] [CharZero K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

omit [NumberField K] in
/-- Piece (c): with `ℓ ∣ ω + θ`, the reduced paired equation at any index `a`
pins `φ(η_a)^k = (−φ(θ))^k` at every reduction hom. -/
theorem eta_pow_k_eq (hζ : IsPrimitiveRoot ζ p)
    {t' : ℕ} (hμ' : IsPrimitiveRoot (redRoot p ℓ t') p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p)
    {ω θ : 𝓞 K} (hsum : ((ℓ : ℕ) : 𝓞 K) ∣ (ω + θ))
    (hcop : ∃ r s : 𝓞 K, r * ω + s * θ = 1)
    {a : ℕ} (ha : ¬ p ∣ a) {ηa : (𝓞 K)ˣ} {ρa : 𝓞 K}
    (heqa : ω + hζ.toInteger ^ a * θ
      = (1 - hζ.toInteger ^ a) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa ^ p) :
    redHom hζ hμ' ((ηa : (𝓞 K)ˣ) : 𝓞 K) ^ k = (- redHom hζ hμ' θ) ^ k := by
  have hφζ : redHom hζ hμ' hζ.toInteger = redRoot p ℓ t' := redHom_zeta hζ hμ'
  have hωθ : redHom hζ hμ' ω + redHom hζ hμ' θ = 0 := by
    have h := redHom_eq_zero_of_dvd hζ hμ' hsum
    rwa [map_add] at h
  have hφθ : redHom hζ hμ' θ ≠ 0 := by
    intro h0
    have hφω : redHom hζ hμ' ω = 0 := by rw [h0, add_zero] at hωθ; exact hωθ
    obtain ⟨r, s, hrs⟩ := hcop
    have h1 := congrArg (redHom hζ hμ') hrs
    rw [map_add, map_mul, map_mul, hφω, h0, mul_zero, mul_zero, add_zero,
      map_one] at h1
    exact zero_ne_one h1
  have h1 := congrArg (redHom hζ hμ') heqa
  rw [map_add, map_mul, map_pow, hφζ, map_mul, map_mul, map_sub, map_one,
    map_pow, hφζ, map_pow] at h1
  have hμa : (1 : ZMod ℓ) - redRoot p ℓ t' ^ a ≠ 0 := by
    intro h0
    have h2 : redRoot p ℓ t' ^ a = 1 := by linear_combination -h0
    exact ha ((hμ'.pow_eq_one_iff_dvd a).mp h2)
  have h3 : (1 - redRoot p ℓ t' ^ a)
      * (redHom hζ hμ' ((ηa : (𝓞 K)ˣ) : 𝓞 K) * redHom hζ hμ' ρa ^ p
        + redHom hζ hμ' θ) = 0 := by
    linear_combination hωθ - h1
  have hkey : redHom hζ hμ' ((ηa : (𝓞 K)ˣ) : 𝓞 K) * redHom hζ hμ' ρa ^ p
      = - redHom hζ hμ' θ := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hμa
    · linear_combination h4
  have hφρ : redHom hζ hμ' ρa ≠ 0 := by
    intro h0
    rw [h0, zero_pow hpri.out.ne_zero, mul_zero] at hkey
    exact hφθ (by linear_combination hkey)
  have h5 := congrArg (· ^ k) hkey
  rw [mul_pow, ← pow_mul, show p * k = ℓ - 1 from by rw [mul_comm]; exact hℓk.symm,
    ZMod.pow_card_sub_one_eq_one hφρ, mul_one] at h5
  exact h5

omit [NumberField K] in
/-- Piece (c), ratio form: the η-ratio dies to the `k` at every hom. -/
theorem eta_ratio_pow_k_eq_one (hζ : IsPrimitiveRoot ζ p)
    {t' : ℕ} (hμ' : IsPrimitiveRoot (redRoot p ℓ t') p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p)
    {ω θ : 𝓞 K} (hsum : ((ℓ : ℕ) : 𝓞 K) ∣ (ω + θ))
    (hcop : ∃ r s : 𝓞 K, r * ω + s * θ = 1)
    {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    {ηa ηb : (𝓞 K)ˣ} {ρa ρb : 𝓞 K}
    (heqa : ω + hζ.toInteger ^ a * θ
      = (1 - hζ.toInteger ^ a) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa ^ p)
    (heqb : ω + hζ.toInteger ^ b * θ
      = (1 - hζ.toInteger ^ b) * ((ηb : (𝓞 K)ˣ) : 𝓞 K) * ρb ^ p) :
    redHom hζ hμ' ((ηa * ηb⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ k = 1 := by
  have hA := eta_pow_k_eq hζ hμ' hℓk hsum hcop ha heqa
  have hB := eta_pow_k_eq hζ hμ' hℓk hsum hcop hb heqb
  have hφηb : redHom hζ hμ' ((ηb : (𝓞 K)ˣ) : 𝓞 K) ≠ 0 :=
    (ηb.isUnit.map (redHom hζ hμ')).ne_zero
  have h6 : redHom hζ hμ' ((ηa * ηb⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ^ k
      * redHom hζ hμ' ((ηb : (𝓞 K)ˣ) : 𝓞 K) ^ k
      = redHom hζ hμ' ((ηb : (𝓞 K)ˣ) : 𝓞 K) ^ k := by
    rw [← mul_pow, ← map_mul,
      show ((ηa * ηb⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((ηb : (𝓞 K)ˣ) : 𝓞 K)
        = ((ηa : (𝓞 K)ˣ) : 𝓞 K) from by rw [← Units.val_mul, inv_mul_cancel_right],
      hA, ← hB]
  exact mul_right_cancel₀ (pow_ne_zero k hφηb) (h6.trans (one_mul _).symm)

/-- **Washington Lemma 9.9** (multi-index form): a real unit whose `k`-th
power dies at every reduction hom above `ℓ` is globally a `p`-th power of a
real unit.  Requires the certificate at EVERY even index — it powers both the
eigen span and the per-index `pDlog` kill. -/
theorem lemma_9_9 [NumberField.IsCMField K]
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hℓ : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    (hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1)
    {ε : (𝓞 K)ˣ} (hεreal : ε ∈ realUnits K)
    (hφε : ∀ (t' : ℕ) (hμ' : IsPrimitiveRoot (redRoot p ℓ t') p),
      redHom hζ hμ' (ε : 𝓞 K) ^ ((ℓ - 1) / p) = 1) :
    ∃ v : (𝓞 K)ˣ, v ∈ realUnits K ∧ ε = v ^ p := by
  classical
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  have hkval : (ℓ - 1) / p = k := by
    rw [hℓk]
    exact Nat.mul_div_cancel k hpri.out.pos
  have hℓ2 : 2 ≤ ℓ := hℓpri.out.two_le
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hℓk
    omega
  -- certificate hygiene for prop_8_18
  have hμ0 : redRoot p ℓ t ≠ 0 := hμ.ne_zero hpri.out.ne_zero
  have ht0 : (t : ZMod ℓ) ≠ 0 := by
    intro h0
    apply hμ0
    rw [redRoot, h0]
    exact zero_pow (by rw [hkval]; exact hk1)
  have ht1 : (t : ZMod ℓ) ^ (ℓ - 1) = 1 := ZMod.pow_card_sub_one_eq_one ht0
  have htk : (t : ZMod ℓ) ^ ((ℓ - 1) / p) ≠ 1 := fun h1 =>
    hμ.ne_one (by omega) (show redRoot p ℓ t = 1 from h1)
  have hkeven' : 2 ∣ (ℓ - 1) / p := by rw [hkval]; exact hkeven
  -- eigen nonvanishing at every even index, hence the span
  have hne : ∀ k' : Fin ((p - 3) / 2), eigenFamily hζ hp2 k' ≠ 0 := by
    intro k'
    have hip : 2 * (k'.1 + 1) ≤ p - 3 := by
      have := k'.2
      omega
    exact prop_8_18 hζ hp2 (2 * (k'.1 + 1)) (even_two_mul _) (by omega) hip
      hℓ ht1 htk hkeven' (hQall _ (even_two_mul _) (by omega) hip)
  obtain ⟨g₀, hg₀⟩ := exists_primRoot_pow_inj (p := p)
  have hspan := eigenFamily_span hζ hp2 g₀ hg₀ hne
  -- decompose the class of ε over the eigen family
  set E : realUnits K := ⟨ε, hεreal⟩ with hE
  have hmem : (vOf E : ModN (Additive (realUnits K)) p)
      ∈ Submodule.span (ZMod p) (Set.range (eigenFamily hζ hp2)) := by
    rw [hspan]
    exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨d, hd⟩ := hmem
  -- multiplicative extraction: ε = ∏ Eᵢ^{dᵢ} · w^p
  set Ei : Fin ((p - 3) / 2) → realUnits K := fun k' =>
    ⟨eigenCyclotomicUnit hζ (2 * (k'.1 + 1)),
      eigenCyclotomicUnit_mem_realUnits hζ hp2 _⟩ with hEi
  set P : realUnits K := ∏ k', Ei k' ^ (d k').val with hP
  have hvP : (vOf P : ModN (Additive (realUnits K)) p) = vOf E := by
    rw [hP, vOf_prod, ← hd]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [vOf_pow, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rfl
  have hz : (vOf (E * P⁻¹) : ModN (Additive (realUnits K)) p) = 0 := by
    rw [vOf_mul, vOf_inv, hvP, add_neg_cancel]
  obtain ⟨w, hw⟩ := (vOf_eq_zero_iff _).mp hz
  have hEPw : E = P * w ^ p := by
    have h := mul_inv_eq_iff_eq_mul.mp hw
    rw [h, mul_comm]
  -- torsion of the certificate values
  have hQtor : ∀ k' : Fin ((p - 3) / 2),
      (qi p (2 * (k'.1 + 1)) ℓ t ^ ((ℓ - 1) / p)) ^ p = 1 := by
    intro k'
    have hip : 2 * (k'.1 + 1) ≤ p - 3 := by
      have := k'.2
      omega
    have hE0 : redHom hζ hμ (eigenCyclotomicUnit hζ (2 * (k'.1 + 1)) : 𝓞 K) ≠ 0 :=
      ((eigenCyclotomicUnit hζ _).isUnit.map (redHom hζ hμ)).ne_zero
    rw [← redHom_eigen_pow_eq_Qi_pow (hζ := hζ) (hμ := hμ) (i := 2 * (k'.1 + 1))
        (hp := hp2) (hℓ := hℓ) (hkeven := hkeven') (hieven := even_two_mul _)
        (hi2 := by omega) (hip := hip),
      ← pow_mul, show (ℓ - 1) / p * p = ℓ - 1 from by rw [hkval]; exact hℓk.symm,
      ZMod.pow_card_sub_one_eq_one hE0]
  -- the per-conjugate relation, in pDlog form
  have hkillFin : ∀ α : (ZMod p)ˣ,
      ∑ k' : Fin ((p - 3) / 2),
        (d k' * pDlog hμ (qi p (2 * (k'.1 + 1)) ℓ t ^ ((ℓ - 1) / p)))
          * ((α : ZMod p)) ^ (2 * (k'.1 + 1)) = 0 := by
    intro α
    have hμ'' : IsPrimitiveRoot (redRoot p ℓ (t ^ (α : ZMod p).val)) p :=
      isPrimitiveRoot_redRoot_pow hμ α
    set J : realUnits K →* ZMod ℓ :=
      (redHom hζ hμ'').toRingHom.toMonoidHom.comp
        ((Units.coeHom (𝓞 K)).comp (realUnits K).subtype) with hJ
    have hJapp : ∀ u : realUnits K,
        J u = redHom hζ hμ'' ((u : (𝓞 K)ˣ) : 𝓞 K) := fun _ => rfl
    have h2 : J E ^ ((ℓ - 1) / p) = 1 := hφε (t ^ (α : ZMod p).val) hμ''
    have hJw : J w ≠ 0 :=
      ((w : (𝓞 K)ˣ).isUnit.map (redHom hζ hμ'')).ne_zero
    have h4 : J P ^ ((ℓ - 1) / p) = 1 := by
      have h5 := congrArg (· ^ ((ℓ - 1) / p)) (congrArg J hEPw)
      simp only [map_mul, map_pow] at h5
      rw [h2, mul_pow, ← pow_mul,
        show p * ((ℓ - 1) / p) = ℓ - 1 from by rw [hkval, mul_comm]; exact hℓk.symm,
        ZMod.pow_card_sub_one_eq_one hJw, mul_one] at h5
      exact h5.symm
    have h7 : ∀ k' : Fin ((p - 3) / 2),
        J (Ei k') ^ ((ℓ - 1) / p)
          = (qi p (2 * (k'.1 + 1)) ℓ t ^ ((ℓ - 1) / p))
              ^ (((α : ZMod p)) ^ (2 * (k'.1 + 1))).val := by
      intro k'
      have hip : 2 * (k'.1 + 1) ≤ p - 3 := by
        have := k'.2
        omega
      rw [hJapp]
      exact redHom_conj_eigen_pow hζ hp2 hℓ hkeven' hμ α hμ''
        (2 * (k'.1 + 1)) (even_two_mul _) (by omega) hip
    have h10 : (1 : ZMod ℓ)
        = ∏ k' : Fin ((p - 3) / 2),
            ((qi p (2 * (k'.1 + 1)) ℓ t ^ ((ℓ - 1) / p))
                ^ (((α : ZMod p)) ^ (2 * (k'.1 + 1))).val) ^ (d k').val := by
      rw [← h4, hP, map_prod, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun k' _ => ?_
      rw [map_pow, ← pow_mul, mul_comm ((d k').val), pow_mul, h7 k']
    have h11 := congrArg (pDlog hμ) h10
    rw [pDlog_one hμ,
      pDlog_prod hμ _ _ (fun k' _ => pow_p_torsion (pow_p_torsion (hQtor k') _) _)]
      at h11
    have h12 : ∀ k' : Fin ((p - 3) / 2),
        pDlog hμ (((qi p (2 * (k'.1 + 1)) ℓ t ^ ((ℓ - 1) / p))
            ^ (((α : ZMod p)) ^ (2 * (k'.1 + 1))).val) ^ (d k').val)
          = (d k' * pDlog hμ (qi p (2 * (k'.1 + 1)) ℓ t ^ ((ℓ - 1) / p)))
              * ((α : ZMod p)) ^ (2 * (k'.1 + 1)) := by
      intro k'
      rw [pDlog_pow hμ (pow_p_torsion (hQtor k') _),
        pDlog_pow hμ (hQtor k'), ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      ring
    rw [Finset.sum_congr rfl fun k' _ => h12 k'] at h11
    exact h11.symm
  -- Vandermonde kill over the ℕ-indexed reindexing
  set F : ℕ → ZMod p := fun m =>
    if h : m < (p - 3) / 2 then
      d ⟨m, h⟩ * pDlog hμ (qi p (2 * (m + 1)) ℓ t ^ ((ℓ - 1) / p))
    else 0 with hF
  have hrel : ∀ α : (ZMod p)ˣ,
      ∑ m ∈ Finset.range ((p - 3) / 2),
        F m * ((α : ZMod p)) ^ (2 * (m + 1)) = 0 := by
    intro α
    calc ∑ m ∈ Finset.range ((p - 3) / 2), F m * ((α : ZMod p)) ^ (2 * (m + 1))
        = ∑ k' : Fin ((p - 3) / 2), F k'.1 * ((α : ZMod p)) ^ (2 * (k'.1 + 1)) :=
          (Fin.sum_univ_eq_sum_range
            (fun m => F m * ((α : ZMod p)) ^ (2 * (m + 1))) _).symm
      _ = ∑ k' : Fin ((p - 3) / 2),
            (d k' * pDlog hμ (qi p (2 * (k'.1 + 1)) ℓ t ^ ((ℓ - 1) / p)))
              * ((α : ZMod p)) ^ (2 * (k'.1 + 1)) := by
          refine Finset.sum_congr rfl fun k' _ => ?_
          rw [hF]
          simp only
          rw [dif_pos k'.2]
      _ = 0 := hkillFin α
  have hkillN := vandermonde_kill (p := p) hp (s := Finset.range ((p - 3) / 2))
    (f := F) (c := fun m => 2 * (m + 1))
    (fun i hi i' hi' hmod => by
      have hi1 := Finset.mem_range.mp hi
      have hi2 := Finset.mem_range.mp hi'
      have hlt : 2 * (i + 1) < p - 1 := by omega
      have hlt' : 2 * (i' + 1) < p - 1 := by omega
      rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at hmod
      omega)
    hrel
  have hd0 : ∀ k' : Fin ((p - 3) / 2), d k' = 0 := by
    intro k'
    have hFk := hkillN k'.1 (Finset.mem_range.mpr k'.2)
    rw [hF] at hFk
    simp only at hFk
    rw [dif_pos k'.2] at hFk
    have hip : 2 * (k'.1 + 1) ≤ p - 3 := by
      have := k'.2
      omega
    have hqne : pDlog hμ (qi p (2 * (k'.1 + 1)) ℓ t ^ ((ℓ - 1) / p)) ≠ 0 := by
      rw [Ne, pDlog_eq_zero_iff hμ (hQtor k')]
      exact hQall _ (even_two_mul _) (by omega) hip
    rcases mul_eq_zero.mp hFk with h | h
    · exact h
    · exact absurd h hqne
  have hvE : (vOf E : ModN (Additive (realUnits K)) p) = 0 := by
    rw [← hd]
    exact Finset.sum_eq_zero fun k' _ => by rw [hd0 k', zero_smul]
  obtain ⟨v, hv⟩ := (vOf_eq_zero_iff _).mp hvE
  exact ⟨(v : (𝓞 K)ˣ), v.2,
    congrArg (fun u : realUnits K => (u : (𝓞 K)ˣ)) hv⟩

/-- **Assumption II from ℓ-data** — the 9.5-route replacement for the depth
certificate: under `ℓ ∣ ω + θ`, the (real) η's of any two paired equations
differ by a global `p`-th power of a real unit. -/
theorem assumption_II_95 [NumberField.IsCMField K]
    (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hℓ : ℓ % p = 1) (hμ : IsPrimitiveRoot (redRoot p ℓ t) p)
    {k : ℕ} (hℓk : ℓ - 1 = k * p) (hkeven : 2 ∣ k)
    (hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1)
    {ω θ : 𝓞 K} (hsum : ((ℓ : ℕ) : 𝓞 K) ∣ (ω + θ))
    (hcop : ∃ r s : 𝓞 K, r * ω + s * θ = 1)
    {a b : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    {ηa ηb : (𝓞 K)ˣ} {ρa ρb : 𝓞 K}
    (hηareal : ηa ∈ realUnits K) (hηbreal : ηb ∈ realUnits K)
    (heqa : ω + hζ.toInteger ^ a * θ
      = (1 - hζ.toInteger ^ a) * ((ηa : (𝓞 K)ˣ) : 𝓞 K) * ρa ^ p)
    (heqb : ω + hζ.toInteger ^ b * θ
      = (1 - hζ.toInteger ^ b) * ((ηb : (𝓞 K)ˣ) : 𝓞 K) * ρb ^ p) :
    ∃ v : (𝓞 K)ˣ, v ∈ realUnits K ∧ ηa = ηb * v ^ p := by
  have hkval : (ℓ - 1) / p = k := by
    rw [hℓk]
    exact Nat.mul_div_cancel k hpri.out.pos
  have hεreal : ηa * ηb⁻¹ ∈ realUnits K :=
    Subgroup.mul_mem _ hηareal (Subgroup.inv_mem _ hηbreal)
  obtain ⟨v, hvreal, hv⟩ := lemma_9_9 hζ hp hℓ hμ hℓk hkeven hQall hεreal
    (fun t' hμ' => by
      rw [hkval]
      exact eta_ratio_pow_k_eq_one hζ hμ' hℓk hsum hcop ha hb heqa heqb)
  refine ⟨v, hvreal, ?_⟩
  rw [← hv, mul_comm ηb, inv_mul_cancel_right]

end Join

end FltVandiver.Descent95
