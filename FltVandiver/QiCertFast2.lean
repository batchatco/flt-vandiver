import QiEvalFast
import FltVandiver.QiCertFast

/-!
# Soundness bridge: `fast2Cert = true → vandiverCert = true`

Every table fact is re-verified inside `fast2Cert`, so the proof only reads
those verified equalities; it never reasons about how a table was built.
-/

namespace FltVandiver.QiCert.Fast2

open CertKernel Finset

theorem sumMod_eq (f : ℕ → ℕ) {p : ℕ} (_hp : 0 < p) :
    ∀ n acc, sumMod f p n acc = (acc + ∑ b ∈ Finset.Icc 1 n, f b) % p := by
  intro n
  induction n with
  | zero => intro acc; simp [sumMod]
  | succ n ih =>
    intro acc
    rw [sumMod, ih, Finset.sum_Icc_succ_top (by omega), Nat.mod_add_mod]
    congr 1
    ring

theorem powTable_chain {gpow : Array ℕ} {g p n : ℕ} (h0 : gpow.getD 0 0 = 1 % p)
    (hstep : ∀ j, j < n → gpow.getD (j + 1) 0 = gpow.getD j 0 * g % p) :
    ∀ m, m ≤ n → gpow.getD m 0 = g ^ m % p := by
  intro m
  induction m with
  | zero => intro _; simpa using h0
  | succ m ih =>
    intro hm
    rw [hstep m (by omega), ih (by omega), pow_succ, Nat.mul_mod (g ^ m) g p,
      Nat.mul_mod (g ^ m % p) g p, Nat.mod_mod]

/-- `powModK` seen in `ZMod`. -/
theorem powModK_cast (t ℓ e : ℕ) (hℓ : 1 ≤ ℓ) :
    ((powModK t ℓ e : ℕ) : ZMod ℓ) = (t : ZMod ℓ) ^ e := by
  rw [powModK_spec t ℓ hℓ, ZMod.natCast_mod, Nat.cast_pow]

/-- A `Nat` below `ℓ` that casts to `1` in `ZMod ℓ` is `1`. -/
theorem eq_one_of_cast_eq_one {ℓ n : ℕ} (hℓ : 2 ≤ ℓ) (hn : n < ℓ)
    (h : (n : ZMod ℓ) = 1) : n = 1 := by
  have h' : (n : ZMod ℓ) = ((1 : ℕ) : ZMod ℓ) := by rw [h, Nat.cast_one]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)] at h'
  exact h'

/-- Soundness of one index test, given the verified table facts. -/
theorem checkIndex_sound {p ℓ t : ℕ} [hp : Fact p.Prime] [hℓ : Fact ℓ.Prime]
    {k half N h g : ℕ} {gpow ind c : Array ℕ}
    (hk : k = (ℓ - 1) / p) (hhalf : half = (p - 1) / 2) (hN : N = k / 2)
    (hh : h = powModK t ℓ k)
    (hℓp : ℓ % p = 1) (hh1 : h ≠ 1) (hu : powModK t ℓ (ℓ - 1) = 1) (h2k : k % 2 = 0)
    (hg0 : 0 < g) (hgp : g < p)
    (hg1 : gpow.getD 0 0 = 1 % p)
    (hchain : ∀ j, j < p - 2 → gpow.getD (j + 1) 0 = gpow.getD j 0 * g % p)
    (hind : ∀ b, 1 ≤ b → b ≤ p - 1 → ind.getD b 0 < p - 1 ∧ gpow.getD (ind.getD b 0) 0 = b)
    (hc : ∀ b, 1 ≤ b → b ≤ half →
      powModK h ℓ (c.getD b 0) = powModK ((powModK h ℓ b + (ℓ - 1)) % ℓ) ℓ k)
    {i : ℕ} (hi3 : i + 3 ≤ p)
    (hi : checkIndex p (p - 1) half N c gpow ind i = true) :
    (qi p i ℓ t) ^ k ≠ 1 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  have hp0 : 0 < p := by omega
  have hℓpos : 1 ≤ ℓ := by omega
  unfold checkIndex at hi
  simp only [bne_iff_ne, ne_eq] at hi
  set e := p - 1 - i with he
  -- the power table gives b^e mod p
  have hw : ∀ b, 1 ≤ b → b ≤ half →
      ((gpow.getD ((e * ind.getD b 0) % (p - 1)) 0 : ℕ) : ZMod p) = (b : ZMod p) ^ e := by
    intro b hb1 hb2
    have hbp : b ≤ p - 1 := by omega
    obtain ⟨hindlt, hindeq⟩ := hind b hb1 hbp
    have hm0 : (e * ind.getD b 0) % (p - 1) ≤ p - 2 := by
      have := Nat.mod_lt (e * ind.getD b 0) (show 0 < p - 1 by omega)
      omega
    rw [powTable_chain hg1 hchain _ hm0, ZMod.natCast_mod, Nat.cast_pow]
    have hgne : (g : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt hg0 hgp
    rw [← pow_mod_card_sub_one (g : ZMod p) hgne, pow_mul']
    congr 1
    have := powTable_chain hg1 hchain _ (by omega : ind.getD b 0 ≤ p - 2)
    rw [this] at hindeq
    have hcast := congrArg (fun n : ℕ => (n : ZMod p)) hindeq
    simpa [ZMod.natCast_mod, Nat.cast_pow] using hcast
  -- the sums
  have hS : ((sumMod (fun b => c.getD b 0 * gpow.getD ((e * ind.getD b 0) % (p - 1)) 0)
      p half 0 : ℕ) : ZMod p)
      = ((∑ b ∈ Finset.Icc 1 half, c.getD b 0 * b ^ e : ℕ) : ZMod p) := by
    rw [sumMod_eq _ hp0, zero_add, ZMod.natCast_mod, Nat.cast_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_Icc] at hb
    rw [Nat.cast_mul, Nat.cast_mul, hw b hb.1 hb.2, Nat.cast_pow]
  have hD : ((sumMod (fun b => b * gpow.getD ((e * ind.getD b 0) % (p - 1)) 0)
      p half 0 : ℕ) : ZMod p) = ((dVal p i : ℕ) : ZMod p) := by
    rw [sumMod_eq _ hp0, zero_add, ZMod.natCast_mod, dVal, ← hhalf, Nat.cast_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_Icc] at hb
    rw [Nat.cast_mul, hw b hb.1 hb.2, Nat.cast_pow, ← pow_succ']
    congr 1
    omega
  -- the check, as a non-congruence
  have hcheck : ¬ ((∑ b ∈ Finset.Icc 1 half, c.getD b 0 * b ^ e) ≡ N * dVal p i [MOD p]) := by
    intro hmod
    apply hi
    have h1 := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hS
    have h2 := (ZMod.natCast_eq_natCast_iff' _ _ p).mp hD
    rw [h1, Nat.mul_mod, h2, ← Nat.mul_mod]
    exact hmod
  -- the element h = t^k of order p in ZMod ℓ
  set hZ : ZMod ℓ := (t : ZMod ℓ) ^ k with hhZ
  have hdvd : p ∣ ℓ - 1 := by
    have h := @Nat.dvd_sub_mod p ℓ
    rwa [hℓp] at h
  have hkp : k * p = ℓ - 1 := by rw [hk]; exact Nat.div_mul_cancel hdvd
  have hu' : (t : ZMod ℓ) ^ (ℓ - 1) = 1 := by
    have := congrArg (fun n : ℕ => (n : ZMod ℓ)) hu
    simpa [powModK_cast t ℓ (ℓ - 1) hℓpos] using this
  have hZp : hZ ^ p = 1 := by rw [hhZ, ← pow_mul, hkp, hu']
  have hhcast : (h : ZMod ℓ) = hZ := by rw [hh, powModK_cast t ℓ k hℓpos]
  have hZ1 : hZ ≠ 1 := by
    intro h1
    apply hh1
    have hlt : h < ℓ := by rw [hh, powModK_spec t ℓ hℓpos]; exact Nat.mod_lt _ (by omega)
    exact eq_one_of_cast_eq_one hℓ2 hlt (by rw [hhcast, h1])
  have hord : orderOf hZ = p := orderOf_eq_prime hZp hZ1
  have hZ0 : hZ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.out.ne_zero] at hZp
    exact zero_ne_one hZp
  -- each factor: (h^b − 1)^k = h^{c_b}
  have hℓm1 : ((ℓ - 1 : ℕ) : ZMod ℓ) = -1 := by
    rw [Nat.cast_sub hℓpos, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hfac : ∀ b, 1 ≤ b → b ≤ half → (hZ ^ b - 1) ^ k = hZ ^ (c.getD b 0) := by
    intro b hb1 hb2
    have key := congrArg (fun n : ℕ => (n : ZMod ℓ)) (hc b hb1 hb2)
    simp only [powModK_cast _ ℓ _ hℓpos, ZMod.natCast_mod, Nat.cast_add, hhcast, hℓm1] at key
    rw [← sub_eq_add_neg] at key
    exact key.symm
  -- the main identity
  have hk2 : k = 2 * N := by omega
  have hqi : (qi p i ℓ t) ^ k
      = (hZ⁻¹) ^ (N * dVal p i) * hZ ^ (∑ b ∈ Finset.Icc 1 half, c.getD b 0 * b ^ e) := by
    simp only [qi]
    rw [← hk, ← hhalf, ← he]
    rw [show k * dVal p i / 2 = N * dVal p i from by
      rw [hk2, Nat.mul_assoc, Nat.mul_div_cancel_left _ two_pos]]
    rw [mul_pow, ← pow_mul, Nat.mul_comm (N * dVal p i) k, pow_mul, inv_pow, ← hhZ,
      ← Finset.prod_pow]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [Finset.mem_Icc] at hb
    rw [← pow_mul, Nat.mul_comm (b ^ e) k, pow_mul ((t : ZMod ℓ) ^ (k * b) - 1) k (b ^ e),
      pow_mul (t : ZMod ℓ) k b, ← hhZ, hfac b hb.1 hb.2, ← pow_mul]
  -- conclude
  intro hqk
  rw [hqi] at hqk
  have hpow : hZ ^ (N * dVal p i) = hZ ^ (∑ b ∈ Finset.Icc 1 half, c.getD b 0 * b ^ e) := by
    rw [inv_pow] at hqk
    exact (inv_mul_eq_one₀ (pow_ne_zero _ hZ0)).mp hqk
  have hunit : (Units.mk0 hZ hZ0) ^ (N * dVal p i)
      = (Units.mk0 hZ hZ0) ^ (∑ b ∈ Finset.Icc 1 half, c.getD b 0 * b ^ e) := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hpow
  rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, hord] at hunit
  exact hcheck hunit.symm

/-- **The bridge**: a true fast certificate yields the reference `vandiverCert`. -/
theorem vandiverCert_of_fast2 {p ℓ t : ℕ} [hp : Fact p.Prime] [hℓ : Fact ℓ.Prime]
    {irr : List ℕ} (h : fast2Cert p ℓ t irr = true) :
    vandiverCert p ℓ t irr = true := by
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  have hℓpos : 1 ≤ ℓ := by omega
  simp only [fast2Cert, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hℓp, hh1⟩, hu⟩, h2k⟩, hg0, hgp⟩, hg1⟩, hchain⟩, hind⟩, hc⟩, hall⟩ := h
  unfold vandiverCert
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨hℓp, ?_⟩, ?_⟩, Nat.dvd_of_mod_eq_zero h2k⟩, fun i hi => ?_⟩
  · intro h1
    apply hh1
    have hlt : powModK t ℓ ((ℓ - 1) / p) < ℓ := by
      rw [powModK_spec t ℓ hℓpos]; exact Nat.mod_lt _ (by omega)
    exact eq_one_of_cast_eq_one hℓ2 hlt (by rw [powModK_cast t ℓ _ hℓpos, h1])
  · have := congrArg (fun n : ℕ => (n : ZMod ℓ)) hu
    simpa [powModK_cast t ℓ (ℓ - 1) hℓpos] using this
  · obtain ⟨hi3, hchk⟩ := hall i hi
    refine checkIndex_sound rfl rfl rfl rfl hℓp hh1 hu h2k hg0 hgp hg1 hchain
      (fun b hb1 hb2 => ?_) (fun b hb1 hb2 => ?_) hi3 hchk
    · have := hind (b - 1) (by omega)
      rwa [show b - 1 + 1 = b from by omega] at this
    · have := hc (b - 1) (by omega)
      rwa [show b - 1 + 1 = b from by omega] at this

end FltVandiver.QiCert.Fast2
