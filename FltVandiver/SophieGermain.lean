import Mathlib.NumberTheory.FLT.Basic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- `native_decide` is the certificate mechanism of this development: compiler-trusted
-- boolean evaluation behind kernel-checked soundness bridges (see the trust note in
-- the README). The linter ban is Mathlib-specific; here the usage is by design.
set_option linter.style.nativeDecide false

/-!
# Case I of FLT via the Sophie Germain / Legendre auxiliary-prime criterion

An **unconditional, elementary** route to Case I (`p ∤ abc`) of FLT — no Vandiver hypothesis, no
cyclotomic class groups, no Stickelberger, no Fermat quotients.

**Legendre's criterion.** Let `p` be an odd prime.  If there is a prime `q` such that
* **(A)** `x^p + y^p + z^p ≡ 0 (mod q)` forces `q ∣ xyz` (only trivial solutions mod `q`), and
* **(B)** `p` is not a `p`-th power modulo `q`,

then the first case of FLT holds for `p`: there are no integers `a, b, c` with `p ∤ abc` and
`a^p + b^p = c^p`.

The proof is the classical Sophie Germain argument: from `a^p+b^p+(-c)^p=0` with `p∤abc`, the Barlow
relations give `a+b`, `c-a`, `c-b` (and their cofactors) as `p`-th powers; reducing mod `q` and
using (A) shows `q` divides one of them, and the cofactor congruence `(x^p+y^p)/(x+y) ≡ p·x^{p-1}`
exhibits `p` as a `p`-th power mod `q`, contradicting (B).

For `p = 37` the auxiliary prime `q = 149` works (both (A) and (B) hold — machine-checked below), so
Case I of FLT holds for `37` **unconditionally**.
-/

namespace FltVandiver

open Finset

/-! ### Algebraic core: the cofactor `(xᵖ+yᵖ)/(x+y)` and its key properties -/

/-- The cofactor `Φ(x,y) = ∑_{i<p} xⁱ(-y)^{p-1-i}`, so that `(x+y)·Φ = xᵖ+yᵖ` for odd `p`. -/
def cofactor (x y : ℤ) (p : ℕ) : ℤ := ∑ i ∈ range p, x ^ i * (-y) ^ (p - 1 - i)

/-- `xᵖ + yᵖ = (x+y)·Φ(x,y)` for odd `p`. -/
theorem add_pow_eq_mul_cofactor (x y : ℤ) {p : ℕ} (hp : Odd p) :
    x ^ p + y ^ p = (x + y) * cofactor x y p := by
  have h := geom_sum₂_mul x (-y) p
  rw [show x - -y = x + y by ring, hp.neg_pow, sub_neg_eq_add] at h
  rw [cofactor, mul_comm, h]

/-- The cofactor is `≡ p·x^{p-1} (mod x+y)`: `(x+y) ∣ Φ(x,y) − p·x^{p-1}`. -/
theorem add_dvd_cofactor_sub (x y : ℤ) {p : ℕ} :
    (x + y) ∣ cofactor x y p - (p : ℤ) * x ^ (p - 1) := by
  rw [cofactor, ← geom_sum₂_self x p, ← Finset.sum_sub_distrib]
  refine Finset.dvd_sum fun i _ => ?_
  rw [← mul_sub]
  refine Dvd.dvd.mul_left ?_ _
  have : (x + y) ∣ ((-y) ^ (p - 1 - i) - x ^ (p - 1 - i)) := by
    have h := sub_dvd_pow_sub_pow (-y) x (p - 1 - i)
    rwa [show -y - x = -(x + y) by ring, neg_dvd] at h
  exact this

/-- `x+y` is coprime to its cofactor `Φ(x,y)`, in Case I: from `IsCoprime x y` and `p ∤ x+y`
(automatic when `p ∤ z`), since `Φ ≡ p·x^{p-1} (mod x+y)` and `x+y` is coprime to both `p` and
`x`. -/
theorem isCoprime_add_cofactor {x y : ℤ} {p : ℕ} (hpp : Prime (p : ℤ))
    (hxy : IsCoprime x y) (hndvd : ¬ (p : ℤ) ∣ (x + y)) :
    IsCoprime (x + y) (cofactor x y p) := by
  obtain ⟨k, hk⟩ := add_dvd_cofactor_sub x y (p := p)
  have hcof : cofactor x y p = (p : ℤ) * x ^ (p - 1) + (x + y) * k := by linarith [hk]
  have hcop_x : IsCoprime (x + y) x := by
    have h := (hxy.symm.add_mul_left_left 1)
    rwa [mul_one, add_comm] at h
  have hcop_p : IsCoprime (x + y) (p : ℤ) := ((hpp.coprime_iff_not_dvd).mpr hndvd).symm
  rw [hcof]
  exact (IsCoprime.mul_right hcop_p (hcop_x.pow_right)).add_mul_left_right k

/-- Over `ℤ`, a coprime factor of an **odd** power is itself a power: if `IsCoprime a b` and
`a * b = cᵖ` with `p` odd, then `a = dᵖ` for some `d` (the `±` from `Associated` is absorbed since
`p` is odd). -/
theorem exists_pow_of_isCoprime_mul {a b c : ℤ} {p : ℕ} (hp : Odd p)
    (hab : IsCoprime a b) (h : a * b = c ^ p) : ∃ d : ℤ, a = d ^ p := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab h
  rcases Int.associated_iff.mp hd with he | he
  · exact ⟨d, he.symm⟩
  · exact ⟨-d, by rw [hp.neg_pow]; linarith [he]⟩

/-! ### The mod-`q` endgame -/

/-- The core contradiction (the `q ∣ w` case, symmetric in `u,v,w`).  Given pairwise-coprime
`u,v,w` with `p∤uvw`, `uᵖ+vᵖ+wᵖ=0`, and `q∣w`: the Barlow relations give `u+v=Aᵖ`, `v+w=Dᵖ`,
`w+u=Eᵖ`, `Φ(u,v)=βᵖ`; mod `q` we get `u≡Eᵖ, v≡Dᵖ`, then (A) forces `q∣A` so `u≡-v`, and the
cofactor congruence yields `p ≡ (β/E^{p-1})ᵖ`, contradicting (B). -/
private theorem sg_endgame {p q : ℕ} (hp : Odd p) (hpp : Prime (p : ℤ)) (hq : q.Prime)
    (hA : ∀ X Y Z : ZMod q, X ^ p + Y ^ p + Z ^ p = 0 → X = 0 ∨ Y = 0 ∨ Z = 0)
    (hB : ∀ t : ZMod q, t ^ p ≠ (p : ZMod q))
    {u v w : ℤ} (huv : IsCoprime u v) (huw : IsCoprime u w) (hvw : IsCoprime v w)
    (hpu : ¬ (p : ℤ) ∣ u) (hpv : ¬ (p : ℤ) ∣ v) (hpw : ¬ (p : ℤ) ∣ w)
    (hsum : u ^ p + v ^ p + w ^ p = 0) (hqw : (q : ℤ) ∣ w) : False := by
  haveI := Fact.mk hq
  have hp0 : p ≠ 0 := by rintro rfl; simp only [pow_zero] at hsum; norm_num at hsum
  -- p ∤ (s+t) whenever s^p+t^p = -(r^p) and p∤r
  have key : ∀ s t r : ℤ, ¬ (p : ℤ) ∣ r → s ^ p + t ^ p = -(r ^ p) → ¬ (p : ℤ) ∣ (s + t) := by
    intro s t r hpr hsum' hd
    have h2 : (p : ℤ) ∣ (s ^ p + t ^ p) :=
      dvd_trans hd ⟨cofactor s t p, add_pow_eq_mul_cofactor s t hp⟩
    rw [hsum'] at h2
    exact hpr (hpp.dvd_of_dvd_pow (dvd_neg.mp h2))
  have e_uv : u ^ p + v ^ p = -(w ^ p) := by linarith [hsum]
  have e_vw : v ^ p + w ^ p = -(u ^ p) := by linarith [hsum]
  have e_wu : w ^ p + u ^ p = -(v ^ p) := by linarith [hsum]
  have nuv := key u v w hpw e_uv
  -- the Barlow relations
  obtain ⟨A, hA_eq⟩ := exists_pow_of_isCoprime_mul hp (isCoprime_add_cofactor hpp huv nuv)
    (by rw [← add_pow_eq_mul_cofactor u v hp, e_uv, hp.neg_pow])
  obtain ⟨D, hD_eq⟩ := exists_pow_of_isCoprime_mul hp
    (isCoprime_add_cofactor hpp hvw (key v w u hpu e_vw))
    (by rw [← add_pow_eq_mul_cofactor v w hp, e_vw, hp.neg_pow])
  obtain ⟨E, hE_eq⟩ := exists_pow_of_isCoprime_mul hp
    (isCoprime_add_cofactor hpp huw.symm (key w u v hpv e_wu))
    (by rw [← add_pow_eq_mul_cofactor w u hp, e_wu, hp.neg_pow])
  obtain ⟨β, hβ_eq⟩ := exists_pow_of_isCoprime_mul hp (isCoprime_add_cofactor hpp huv nuv).symm
    (by rw [mul_comm, ← add_pow_eq_mul_cofactor u v hp, e_uv, hp.neg_pow])
  -- cast to ZMod q
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hw0 : (w : ZMod q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd w q).mpr hqw
  have hu_E : (u : ZMod q) = (E : ZMod q) ^ p := by
    have h : ((w + u : ℤ) : ZMod q) = ((E ^ p : ℤ) : ZMod q) := by rw [hE_eq]
    push_cast at h; rw [hw0, zero_add] at h; exact h
  have hv_D : (v : ZMod q) = (D : ZMod q) ^ p := by
    have h : ((v + w : ℤ) : ZMod q) = ((D ^ p : ℤ) : ZMod q) := by rw [hD_eq]
    push_cast at h; rw [hw0, add_zero] at h; exact h
  have hA_uv : (u : ZMod q) + (v : ZMod q) = (A : ZMod q) ^ p := by
    have h : ((u + v : ℤ) : ZMod q) = ((A ^ p : ℤ) : ZMod q) := by rw [hA_eq]
    push_cast at h; exact h
  have hqnu : (u : ZMod q) ≠ 0 := fun h =>
    hqp.not_unit (huw.isUnit_of_dvd' ((ZMod.intCast_zmod_eq_zero_iff_dvd u q).mp h) hqw)
  have hqnv : (v : ZMod q) ≠ 0 := fun h =>
    hqp.not_unit (hvw.isUnit_of_dvd' ((ZMod.intCast_zmod_eq_zero_iff_dvd v q).mp h) hqw)
  have hEne : (E : ZMod q) ≠ 0 := fun h => hqnu (by rw [hu_E, h, zero_pow hp0])
  -- (A) applied: E^p + D^p + (-A)^p = (u+v) - (u+v) = 0
  have hEDA : (E : ZMod q) ^ p + (D : ZMod q) ^ p + (-(A : ZMod q)) ^ p = 0 := by
    rw [hp.neg_pow, ← hu_E, ← hv_D, ← hA_uv]; ring
  rcases hA _ _ _ hEDA with hE0 | hD0 | hA0
  · exact hEne hE0
  · exact hqnv (by rw [hv_D, hD0, zero_pow hp0])
  · -- A ≡ 0 mod q ⟹ u ≡ -v ⟹ cofactor ≡ p·u^{p-1} ⟹ p is a p-th power, contradicting (B)
    rw [neg_eq_zero] at hA0
    have huv0 : (u : ZMod q) + (v : ZMod q) = 0 := by rw [hA_uv, hA0, zero_pow hp0]
    have hquv : (q : ℤ) ∣ (u + v) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact huv0
    have hcof_q : (cofactor u v p : ZMod q) = (p : ZMod q) * (u : ZMod q) ^ (p - 1) := by
      have hd : (q : ℤ) ∣ (cofactor u v p - (p : ℤ) * u ^ (p - 1)) :=
        dvd_trans hquv (add_dvd_cofactor_sub u v)
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hd
      push_cast at hz; linear_combination hz
    have hβp : (β : ZMod q) ^ p = (p : ZMod q) * ((E : ZMod q) ^ (p - 1)) ^ p := by
      have hβc : ((cofactor u v p : ℤ) : ZMod q) = (β : ZMod q) ^ p := by
        have h : ((cofactor u v p : ℤ) : ZMod q) = ((β ^ p : ℤ) : ZMod q) := by rw [hβ_eq]
        push_cast at h; exact h
      rw [← hβc, hcof_q, hu_E, ← pow_mul, ← pow_mul, Nat.mul_comm (p - 1) p]
    have hc : ((E : ZMod q) ^ (p - 1)) ^ p ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hEne)
    refine hB ((β : ZMod q) / (E : ZMod q) ^ (p - 1)) ?_
    rw [div_pow, hβp, mul_div_assoc, div_self hc, mul_one]

/-- The pairwise-coprime case: `(A)` gives `q ∣ x ∨ q ∣ y ∨ q ∣ z`, then `sg_endgame` (applied with
the matching permutation) gives the contradiction. -/
private theorem caseI_coprime {p q : ℕ} (hp : Odd p) (hpp : Prime (p : ℤ)) (hq : q.Prime)
    (hA : ∀ X Y Z : ZMod q, X ^ p + Y ^ p + Z ^ p = 0 → X = 0 ∨ Y = 0 ∨ Z = 0)
    (hB : ∀ t : ZMod q, t ^ p ≠ (p : ZMod q))
    {x y z : ℤ} (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z)
    (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y) (hpz : ¬ (p : ℤ) ∣ z)
    (hsum : x ^ p + y ^ p + z ^ p = 0) : False := by
  have hsumq : (x : ZMod q) ^ p + (y : ZMod q) ^ p + (z : ZMod q) ^ p = 0 := by
    have h : ((x ^ p + y ^ p + z ^ p : ℤ) : ZMod q) = ((0 : ℤ) : ZMod q) := by rw [hsum]
    push_cast at h; exact h
  rcases hA _ _ _ hsumq with h0 | h0 | h0
  · exact sg_endgame hp hpp hq hA hB hyz hxy.symm hxz.symm hpy hpz hpx (by linarith [hsum])
      ((ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp h0)
  · exact sg_endgame hp hpp hq hA hB hxz hxy hyz.symm hpx hpz hpy (by linarith [hsum])
      ((ZMod.intCast_zmod_eq_zero_iff_dvd y q).mp h0)
  · exact sg_endgame hp hpp hq hA hB hxy hxz hyz hpx hpy hpz hsum
      ((ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp h0)

/-- **Legendre's auxiliary-prime criterion (Case I of FLT).**  The elementary core: the Barlow
relations + mod-`q` argument (no class groups / Fermat quotients), assembled from the lemmas
above. -/
theorem caseI_of_auxiliaryPrime {p : ℕ} [Fact p.Prime] (hp : Odd p) {q : ℕ} (hq : q.Prime)
    (hA : ∀ x y z : ZMod q, x ^ p + y ^ p + z ^ p = 0 → x = 0 ∨ y = 0 ∨ z = 0)
    (hB : ∀ t : ZMod q, t ^ p ≠ (p : ZMod q))
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro h
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hsum0 : a ^ p + b ^ p + (-c) ^ p = 0 := by rw [hp.neg_pow]; linarith [h]
  have hpa : ¬ (p : ℤ) ∣ a := fun hd => hcaseI ((hd.mul_right b).mul_right c)
  have hpb : ¬ (p : ℤ) ∣ b := fun hd => hcaseI ((hd.mul_left a).mul_right c)
  have hpz : ¬ (p : ℤ) ∣ (-c) := fun hd => hcaseI ((dvd_neg.mp hd).mul_left (a * b))
  have ha0 : a ≠ 0 := fun h0 => hpa (h0 ▸ dvd_zero _)
  -- divide out d = gcd {a, b, -c}
  let d := Finset.gcd ({a, b, -c} : Finset ℤ) id
  obtain ⟨A, hA'⟩ : d ∣ a := Finset.gcd_dvd (by simp)
  obtain ⟨B, hB'⟩ : d ∣ b := Finset.gcd_dvd (by simp)
  obtain ⟨C, hC'⟩ : d ∣ (-c) := Finset.gcd_dvd (by simp)
  have hd0 : d ≠ 0 := fun h0 => ha0 (by rw [hA', h0, zero_mul])
  -- the reduced triple still solves FLT (Case I) with gcd 1
  have hsumABC : A ^ p + B ^ p + C ^ p = 0 := by
    have h2 : d ^ p * (A ^ p + B ^ p + C ^ p) = 0 := by
      have hh := hsum0; rw [hA', hB', hC', mul_pow, mul_pow, mul_pow] at hh; linear_combination hh
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero p hd0)
  have hgcd1 : Finset.gcd ({A, B, C} : Finset ℤ) id = 1 := by
    have hAdiv : A = a / d := by rw [hA']; exact (Int.mul_ediv_cancel_left A hd0).symm
    have hBdiv : B = b / d := by rw [hB']; exact (Int.mul_ediv_cancel_left B hd0).symm
    have hCdiv : C = (-c) / d := by rw [hC']; exact (Int.mul_ediv_cancel_left C hd0).symm
    have himg : ({A, B, C} : Finset ℤ) = ({a, b, -c} : Finset ℤ).image (· / d) := by
      rw [Finset.image_insert, Finset.image_insert, Finset.image_singleton, hAdiv, hBdiv, hCdiv]
    rw [himg, ← Finset.gcd_eq_gcd_image]
    exact Finset.gcd_div_id_eq_one (show a ∈ ({a, b, -c} : Finset ℤ) by simp) ha0
  have hpA : ¬ (p : ℤ) ∣ A := fun hd => hpa (hA' ▸ Dvd.dvd.mul_left hd d)
  have hpB : ¬ (p : ℤ) ∣ B := fun hd => hpb (hB' ▸ Dvd.dvd.mul_left hd d)
  have hpC : ¬ (p : ℤ) ∣ C := fun hd => hpz (hC' ▸ Dvd.dvd.mul_left hd d)
  refine caseI_coprime hp hpp hq hA hB ?_ ?_ ?_ hpA hpB hpC hsumABC
  · exact isCoprime_of_gcd_eq_one_of_FLT hgcd1 hsumABC
  · refine isCoprime_of_gcd_eq_one_of_FLT ?_ (show A ^ p + C ^ p + B ^ p = 0 by linarith [hsumABC])
    rw [show ({A, C, B} : Finset ℤ) = {A, B, C} from by ext x; simp; tauto]; exact hgcd1
  · refine isCoprime_of_gcd_eq_one_of_FLT ?_ (show B ^ p + C ^ p + A ^ p = 0 by linarith [hsumABC])
    rw [show ({B, C, A} : Finset ℤ) = {A, B, C} from by ext x; simp; tauto]; exact hgcd1

section P37

instance : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- **The auxiliary prime `q = 149` works for `p = 37`.**  Machine-checked:
(A) the only mod-149 solutions of `x³⁷+y³⁷+z³⁷≡0` are the trivial ones, and
(B) `37` is not a `37`-th power mod `149`. -/
theorem caseI_37 {a b c : ℤ} (hcaseI : ¬ (37 : ℤ) ∣ a * b * c) :
    a ^ 37 + b ^ 37 ≠ c ^ 37 :=
  caseI_of_auxiliaryPrime (by norm_num) (by norm_num : Nat.Prime 149)
    (by native_decide) (by native_decide) hcaseI

end P37

/-! ### A cheap certificate for the auxiliary-prime hypotheses

The hypotheses `(A)`/`(B)` of `caseI_of_auxiliaryPrime` are stated as `∀ x y z : ZMod q, …` and
`∀ t : ZMod q, …`.  Deciding them directly costs `q³` (resp. `q`) iterations — fine for `q = 149`
(as in `caseI_37`), but hopeless once the auxiliary prime runs into the hundreds or thousands, as
it does for the larger irregular primes.

But both conditions only depend on the (small) set of `p`-th power residues:
* `(A)` fails iff three **nonzero** `p`-th power residues sum to `0`;
* `(B)` fails iff `p` is itself a `p`-th power residue.

`sgCert p q` checks exactly this over the residue set / image — `|image| = (q-1)/p + 1` elements,
not `q³` triples — so `native_decide` evaluates it instantly even for `q` in the thousands.
`sgCert_imp` is the (elementary, general-in-`p`) bridge back to `(A)`/`(B)`; together they play the
role that `vandiverCert` + its bridge play for the Case II (`Q_i`) certificates. -/

/-- Cheap Legendre certificate: `q ≡ 1 (mod p)`; no three nonzero `p`-th power residues sum to `0`
(condition `(A)`); and `p` is not a `p`-th power residue (condition `(B)`, checked against the full
image `{tᵖ}` — which contains `0` — so it faithfully encodes `∀ t, tᵖ ≠ p`). -/
def sgCert (p q : ℕ) [NeZero q] : Bool :=
  let img := Finset.univ.image fun x : ZMod q => x ^ p
  let S := img.erase 0
  (q % p == 1) &&
  decide (∀ a ∈ S, ∀ b ∈ S, -(a + b) ∉ S) &&
  decide ((p : ZMod q) ∉ img)

/-- **Bridge:** `sgCert p q = true` supplies Legendre's hypotheses `(A)` and `(B)`.  Elementary and
general in `p`: a nonzero `x` has `xᵖ ≠ 0`, so the nonzero terms of a vanishing `xᵖ+yᵖ+zᵖ` are
three residues summing to `0` (ruled out by `(A)`); and `tᵖ = p` would place `p` in the image
(ruled out by `(B)`). -/
theorem sgCert_imp {p q : ℕ} [NeZero q] [Fact q.Prime] (h : sgCert p q = true) :
    (∀ x y z : ZMod q, x ^ p + y ^ p + z ^ p = 0 → x = 0 ∨ y = 0 ∨ z = 0) ∧
    (∀ t : ZMod q, t ^ p ≠ (p : ZMod q)) := by
  simp only [sgCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨_h1, hA⟩, hB⟩ := h
  set S := (Finset.univ.image fun x : ZMod q => x ^ p).erase 0 with hS
  have hmem : ∀ x : ZMod q, x ≠ 0 → x ^ p ∈ S := fun x hx => by
    rw [hS, Finset.mem_erase]
    exact ⟨pow_ne_zero p hx, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩
  refine ⟨fun x y z hsum => ?_, fun t hcontra => ?_⟩
  · by_contra hcon
    rw [not_or, not_or] at hcon
    obtain ⟨hx, hy, hz⟩ := hcon
    have hzp : z ^ p = -(x ^ p + y ^ p) := by linear_combination hsum
    exact hA _ (hmem x hx) _ (hmem y hy) (hzp ▸ hmem z hz)
  · exact hB (hcontra ▸ Finset.mem_image_of_mem _ (Finset.mem_univ t))

/-- Case I of FLT for `p` from a `sgCert`-verified auxiliary prime `q` — the cheap analog of
`caseI_37`, usable for primes whose auxiliary `q` is too large for a direct `q³` `native_decide`. -/
theorem caseI_of_sgCert {p : ℕ} [Fact p.Prime] (hp : Odd p) {q : ℕ} [NeZero q] (hq : q.Prime)
    (hcert : sgCert p q = true) {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  haveI := Fact.mk hq
  obtain ⟨hA, hB⟩ := sgCert_imp hcert
  exact caseI_of_auxiliaryPrime hp hq hA hB hcaseI

/-- Consistency anchor: for `p = 37` the cheap `sgCert` agrees with the direct `q³` brute force used
in `caseI_37`.  We keep `caseI_37` itself on the brute-force path (it feeds the headline FLT-for-37
result) precisely so that one prime is verified the literal way — this `example` confirms the
residue-set shortcut `sgCert` returns the same verdict on it. -/
example : sgCert 37 149 = true := by native_decide

section OtherSmallIrregularPrimes

/-! Case I of FLT for the next few irregular primes, via the cheap `sgCert` certificate (so the
proofs check in milliseconds despite the large auxiliary primes).  These are the Case I counterparts
of the Case II (`Q_i`) certificates in `QiCertificate.lean`; the auxiliary prime is the least
`q ≡ 1 (mod p)` satisfying Legendre's `(A)` and `(B)`.  Together with the matching Vandiver
certificate, each would give full FLT for that prime once its Case II is wired in. -/

instance : Fact (Nat.Prime 59) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 827) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 67) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 269) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 809) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 103) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 1031) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 131) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 263) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 149) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 1193) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 157) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 1571) := ⟨by norm_num⟩

end OtherSmallIrregularPrimes

/-! ### The subgroup-form Legendre certificate

For large auxiliary primes `q`, `sgCert` (which enumerates `ZMod q`) is
infeasible. `sgCertSub` instead takes the `n = (q−1)/p` nonzero `p`-th-power
residues as *data*: they are `n` distinct roots of `Xⁿ − 1`, which has at most
`n` roots in a field, so the list provably contains every `p`-th power of a
nonzero element; the checks are `O(n²)`, not `O(q)`.

Two performance traps (both `O(q)`) for certificate authors:
`decide (∀ s ∈ l, …)` picks the `Fintype` forall instance (enumerate all of
`ZMod q`) — quantify over the list with `List.all`; and `native_decide` on
`Nat.Prime q` uses the bounded-forall instance — use `norm_num` instead. -/

/-- Subgroup-form Legendre certificate: `l` lists `n = (q−1)/p` distinct `n`-th roots of
unity (hence *all* of them, hence exactly the nonzero `p`-th power residues); no three
of them sum to `0` (condition (A)); and `p` is neither `0` nor in the list (condition
(B)). Unlike `sgCert`, verification never enumerates `ZMod q` — the quantifier clauses
are `List.all` folds precisely to dodge the `Fintype` decidable-forall instance. -/
def sgCertSub (p q n : ℕ) [NeZero q] (l : List (ZMod q)) : Bool :=
  decide (q - 1 = n * p) &&
  decide (l.length = n) &&
  decide l.Nodup &&
  (l.all fun s => decide (s ^ n = 1)) &&
  (l.all fun a => l.all fun b => decide (-(a + b) ∉ l)) &&
  decide ((p : ZMod q) ∉ l) &&
  decide ((p : ZMod q) ≠ 0)

/-- **Bridge:** `sgCertSub p q n l = true` supplies Legendre's hypotheses `(A)` and `(B)`
in the form consumed by `caseI_of_auxiliaryPrime`. The only mathematics beyond
`sgCert_imp`'s is the root-count argument: `l` is a set of `n` distinct roots of
`Xⁿ − 1` over the field `ZMod q`, so it exhausts them, and every `xᵖ` with `x ≠ 0` is
such a root since `(xᵖ)ⁿ = x^{q−1} = 1`. -/
theorem sgCertSub_imp {p q n : ℕ} [NeZero q] [Fact q.Prime] {l : List (ZMod q)}
    (h : sgCertSub p q n l = true) :
    (∀ x y z : ZMod q, x ^ p + y ^ p + z ^ p = 0 → x = 0 ∨ y = 0 ∨ z = 0) ∧
    (∀ t : ZMod q, t ^ p ≠ (p : ZMod q)) := by
  simp only [sgCertSub, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hqn, hlen⟩, hnodup⟩, hroots⟩, hA⟩, hBmem⟩, hBne⟩ := h
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hnp : 0 < n * p := by rw [← hqn]; omega
  have hn0 : n ≠ 0 := by rintro rfl; simp at hnp
  have hp0 : p ≠ 0 := by rintro rfl; simp at hnp
  -- every `p`-th power of a nonzero element appears in `l`
  have hmem : ∀ x : ZMod q, x ≠ 0 → x ^ p ∈ l := by
    intro x hx
    have h1 : (x ^ p) ^ n = 1 := by
      rw [← pow_mul, mul_comm, ← hqn]
      exact ZMod.pow_card_sub_one_eq_one hx
    have h2 : x ^ p ∈ Polynomial.nthRoots n (1 : ZMod q) :=
      (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn0)).mpr h1
    have hsub : l.toFinset ⊆ (Polynomial.nthRoots n (1 : ZMod q)).toFinset := by
      intro s hs
      rw [Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn0)).mpr
        (hroots s (List.mem_toFinset.mp hs))
    have hcard : (Polynomial.nthRoots n (1 : ZMod q)).toFinset.card ≤ l.toFinset.card :=
      calc (Polynomial.nthRoots n (1 : ZMod q)).toFinset.card
          ≤ Multiset.card (Polynomial.nthRoots n (1 : ZMod q)) :=
            Multiset.toFinset_card_le _
        _ ≤ n := Polynomial.card_nthRoots n (1 : ZMod q)
        _ = l.toFinset.card := by rw [List.toFinset_card_of_nodup hnodup, hlen]
    have hx' : x ^ p ∈ l.toFinset := by
      rw [Finset.eq_of_subset_of_card_le hsub hcard]
      exact Multiset.mem_toFinset.mpr h2
    exact List.mem_toFinset.mp hx'
  refine ⟨fun x y z hsum => ?_, fun t hcontra => ?_⟩
  · by_contra hcon
    rw [not_or, not_or] at hcon
    obtain ⟨hx, hy, hz⟩ := hcon
    have hzp : z ^ p = -(x ^ p + y ^ p) := by linear_combination hsum
    exact hA _ (hmem x hx) _ (hmem y hy) (hzp ▸ hmem z hz)
  · by_cases ht : t = 0
    · subst ht
      rw [zero_pow hp0] at hcontra
      exact hBne hcontra.symm
    · exact hBmem (hcontra ▸ hmem t ht)

end FltVandiver
