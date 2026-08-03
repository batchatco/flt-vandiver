import FltVandiver.SophieGermain

/-!
# The Germain-window pigeonhole reduction

`sgCert p q` demands two things of an auxiliary prime `q ≡ 1 (mod 2p)`:

* **(A)** no three nonzero `p`-th power residues sum to `0` — equivalently (after
  scaling by the group structure of the residue subgroup `H`), **no two elements of `H`
  sum to `1`**: `sgPairCount p q = 0`;
* **(B)** `p` itself is not a `p`-th power residue: `sgPowFail p q = false`.

This file proves the **pigeonhole assembly**: if the window
`𝒬_p(x) = {q ≤ x prime, q ≡ 1 (mod 2p), 3 ∤ (q−1)/2p}` has at least `M` members
(hypothesis (α), prime supply), the aggregated pair-count satisfies `2·Σ S(q) ≤ M`
(hypothesis (β-A), Jacobi-sum cancellation on average), and at most `M/4` members fail
(B) (hypothesis (β-B)), then some `q` in the window passes `sgCert` — hence Case I at
`p` (`caseI_of_sgCert`).

The `3 ∤ (q−1)/2p` window condition excludes the cube-root obstruction (`ω + ω² + 1 = 0`
forces (A)-failures whenever `3 ∣ |H|`); it is not needed for the pigeonhole's
soundness, only for the plausibility of (β-A), and is kept so the stated hypotheses are
the true ones. By design, (α)/(β-A)/(β-B) are *hypotheses* here — open
analytic number theory, stated exactly, never to be proven in Lean.
-/

namespace FltVandiver

open Finset

/-- The number of pairs `(x, y)` of **nonzero `p`-th power residues** mod `q` with
`x + y = 1` — the normalized count whose vanishing is Legendre's condition (A). -/
def sgPairCount (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | (n+1) =>
    let H := (Finset.univ.image fun x : ZMod (n+1) => x ^ p).erase 0
    ((H ×ˢ H).filter fun z => z.1 + z.2 = 1).card

/-- Condition (B) fails: `p` is a `p`-th power mod `q`. -/
def sgPowFail (p : ℕ) : ℕ → Bool
  | 0 => false
  | (n+1) =>
    decide ((p : ZMod (n+1)) ∈ Finset.univ.image fun x : ZMod (n+1) => x ^ p)

/-- The auxiliary-prime candidate window `𝒬_p(x)`: primes `q ≤ x` with
`q ≡ 1 (mod 2p)` and `3 ∤ (q−1)/2p`. -/
def sgWindow (p x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter
    fun q => q.Prime ∧ q % (2 * p) = 1 ∧ ¬ (3 ∣ (q - 1) / (2 * p))

/-- **The per-prime bridge**: a window prime with vanishing pair count and `(B)` intact
passes `sgCert`. The (A)-direction is the group-theoretic rescaling: a violating triple
`a, b, −(a+b) ∈ H` divides through by `−(a+b)` (using `−1 = (−1)^p ∈ H` for odd `p`) to
produce a pair summing to `1`. -/
theorem sgCert_eq_true_of {p q : ℕ} (hp : Odd p) [NeZero q] [Fact q.Prime]
    (hq1 : q % p = 1) (hS : sgPairCount p q = 0) (hB : sgPowFail p q = false) :
    sgCert p q = true := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 :=
    ⟨q - 1, by have := Nat.pos_of_ne_zero (NeZero.ne q); omega⟩
  rw [sgCert]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨hq1, ?_⟩, ?_⟩
  · -- condition (A) from `sgPairCount = 0`
    intro a ha b hb hcon
    -- names for the residue set and the witnesses
    set H := (Finset.univ.image fun x : ZMod (n+1) => x ^ p).erase 0 with hH
    have hmem : ∀ z : ZMod (n+1), z ∈ H ↔ z ≠ 0 ∧ ∃ t, t ^ p = z := by
      intro z
      rw [hH, Finset.mem_erase]
      simp [Finset.mem_image]
    obtain ⟨ha0, s, hs⟩ := (hmem a).mp ha
    obtain ⟨hb0, u, hu⟩ := (hmem b).mp hb
    obtain ⟨hc0, v, hv⟩ := (hmem _).mp hcon
    -- the rescaled pair (x, y) := (a, b)/(−(a+b))
    have hsum0 : a + b ≠ 0 := by
      intro h0
      rw [h0, neg_zero] at hc0
      exact hc0 rfl
    have hvne : v ≠ 0 := by
      intro h0
      rw [h0] at hv
      have : (0 : ZMod (n+1)) ^ p = 0 :=
        zero_pow (by have := hp.pos; omega)
      rw [this] at hv
      exact hc0 hv.symm
    set w : ZMod (n+1) := (-(v⁻¹)) with hw
    have hwp : w ^ p = (a + b)⁻¹ := by
      rw [hw, Odd.neg_pow hp, inv_pow, hv, inv_neg, neg_neg]
    have hwne : w ≠ 0 := by
      rw [hw, neg_ne_zero]
      exact inv_ne_zero hvne
    have hkey : (a * w ^ p) + (b * w ^ p) = 1 := by
      rw [hwp, ← add_mul]
      exact mul_inv_cancel₀ hsum0
    -- both rescaled coordinates lie in H
    have hx : a * w ^ p ∈ H := (hmem _).mpr ⟨by
        refine mul_ne_zero ha0 (pow_ne_zero _ hwne), ⟨s * w, by rw [mul_pow, hs]⟩⟩
    have hy : b * w ^ p ∈ H := (hmem _).mpr ⟨by
        refine mul_ne_zero hb0 (pow_ne_zero _ hwne), ⟨u * w, by rw [mul_pow, hu]⟩⟩
    -- contradiction with the vanishing pair count
    have hcard : 0 < (((H ×ˢ H).filter fun z => z.1 + z.2 = 1)).card := by
      refine Finset.card_pos.mpr ⟨(a * w ^ p, b * w ^ p), ?_⟩
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hx, hy⟩, hkey⟩
    rw [show sgPairCount p (n+1) = (((H ×ˢ H).filter
        fun z => z.1 + z.2 = 1)).card from rfl] at hS
    omega
  · -- condition (B) from `sgPowFail = false`
    intro hmem
    rw [show sgPowFail p (n+1) = decide ((p : ZMod (n+1))
        ∈ Finset.univ.image fun x : ZMod (n+1) => x ^ p) from rfl] at hB
    simp only [decide_eq_false_iff_not] at hB
    exact hB hmem

/-- **The pigeonhole assembly**: prime supply (α) plus
aggregated Jacobi cancellation (β-A) plus power-residue sparsity (β-B) over the window
produce an `sgCert`-verified auxiliary prime — hence Case I at `p`. -/
theorem sgAux_of_supply_of_cancellation {p : ℕ} (hp : Odd p) (hp1 : 1 < p)
    {x M : ℕ} (hM : 0 < M)
    (hα : M ≤ (sgWindow p x).card)
    (hβA : 2 * ∑ q ∈ sgWindow p x, sgPairCount p q ≤ M)
    (hβB : 4 * ((sgWindow p x).filter fun q => sgPowFail p q = true).card ≤ M) :
    ∃ q : ℕ, ∃ _ : NeZero q, q.Prime ∧ sgCert p q = true := by
  classical
  set 𝒬 := sgWindow p x with h𝒬
  set badA := 𝒬.filter fun q => sgPairCount p q ≠ 0 with hbadA
  set badB := 𝒬.filter fun q => sgPowFail p q = true with hbadB
  -- the bad-A count is dominated by the aggregated pair count
  have h1 : badA.card ≤ ∑ q ∈ 𝒬, sgPairCount p q := by
    calc badA.card = ∑ _q ∈ badA, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ q ∈ badA, sgPairCount p q := by
          refine Finset.sum_le_sum ?_
          intro q hq
          rw [hbadA, Finset.mem_filter] at hq
          omega
      _ ≤ ∑ q ∈ 𝒬, sgPairCount p q := by
          refine Finset.sum_le_sum_of_subset ?_
          rw [hbadA]
          exact Finset.filter_subset _ _
  -- strictly fewer bad members than the window holds
  have h2 : (badA ∪ badB).card < 𝒬.card := by
    have h3 := Finset.card_union_le badA badB
    omega
  -- a good member exists
  have h4 : (𝒬 \ (badA ∪ badB)).Nonempty := by
    rw [← Finset.card_pos]
    have h5 : (badA ∪ badB) ∩ 𝒬 = badA ∪ badB := by
      refine Finset.inter_eq_left.mpr ?_
      refine Finset.union_subset ?_ ?_
      · rw [hbadA]; exact Finset.filter_subset _ _
      · rw [hbadB]; exact Finset.filter_subset _ _
    have h6 := Finset.card_sdiff_add_card_inter 𝒬 (badA ∪ badB)
    rw [Finset.inter_comm, h5] at h6
    omega
  obtain ⟨q, hq⟩ := h4
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hq
  obtain ⟨hqQ, hnotA, hnotB⟩ := hq
  -- unpack the window membership (keep the original for the filter arguments)
  have hqQ' := hqQ
  rw [h𝒬, sgWindow, Finset.mem_filter] at hqQ'
  obtain ⟨_, hqprime, hqmod, _⟩ := hqQ'
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  haveI : Fact q.Prime := ⟨hqprime⟩
  -- q ≡ 1 (mod p) from q ≡ 1 (mod 2p)
  have hq1 : q % p = 1 := by
    have h7 : q = 2 * p * (q / (2 * p)) + 1 := by
      have h8 := Nat.div_add_mod q (2 * p)
      omega
    rw [h7, show 2 * p * (q / (2 * p)) = p * (2 * (q / (2 * p))) from by ring,
      Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hp1
  -- the bad-set escapes give the bridge's hypotheses
  have hS : sgPairCount p q = 0 := by
    by_contra h
    refine hnotA ?_
    rw [hbadA, Finset.mem_filter]
    exact ⟨hqQ, h⟩
  have hB : sgPowFail p q = false := by
    rcases Bool.eq_false_or_eq_true (sgPowFail p q) with h | h
    · refine absurd ?_ hnotB
      rw [hbadB, Finset.mem_filter]
      exact ⟨hqQ, h⟩
    · exact h
  exact ⟨q, inferInstance, hqprime, sgCert_eq_true_of hp hq1 hS hB⟩

/-- **Case I from the window hypotheses** — the form the crown consumes. -/
theorem caseI_of_supply_of_cancellation {p : ℕ} [Fact p.Prime] (hp : Odd p)
    {x M : ℕ} (hM : 0 < M)
    (hα : M ≤ (sgWindow p x).card)
    (hβA : 2 * ∑ q ∈ sgWindow p x, sgPairCount p q ≤ M)
    (hβB : 4 * ((sgWindow p x).filter fun q => sgPowFail p q = true).card ≤ M)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  obtain ⟨q, _, hqprime, hcert⟩ := sgAux_of_supply_of_cancellation hp
    (Fact.out : p.Prime).one_lt hM hα hβA hβB
  exact caseI_of_sgCert hp hqprime hcert hcaseI

end FltVandiver
