import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import FltRegular.NumberTheory.Cyclotomic.CyclRat

/-!
# Descent92 elementary bricks — the `p²`-congruence trick and depth extraction

Architecture-independent lemmas for the Washington §9.1/§9.2-faithful Case II descent
feeding the corrected Kummer lemma `realUnitKummer_M1`
(`KummerM1.lean`):

* `exists_int_pow_p_sq_sub_dvd` — **the `p²`-power trick**: for any `w` in a `p`-th
  cyclotomic ring, `w^{p²} ≡ rational integer (mod p²)`.  This is what turns Washington
  Thm 9.4's congruence `U ≡ (μ_b/μ_a)^{p²} (mod (1−ζ)^{2m−2p})` into the
  `∃ n, p² ∣ U − n` hypothesis of the corrected Kummer lemma.  Elementary:
  `wᵖ ≡ a (mod p)` (Frobenius, `exists_int_sub_pow_prime_dvd`), then
  `(wᵖ)ᵖ ≡ aᵖ (mod p²)` (`dvd_sub_pow_of_dvd_sub`).
* `pow_p_congruence_lift` — `a ≡ b (mod π^k)` ⟹ `aᵖ ≡ bᵖ (mod π^{k+1}·…)`-style depth
  lifting used when substituting the second-level decomposition `ρ ≡ η̃μᵖ` into the first
  level.
-/

namespace FltVandiver.Descent92

open Ideal

variable {p : ℕ} [hpri : Fact p.Prime]

/-- **The `p²`-power trick** (Washington Thm 9.4's congruence input): in a `p`-th cyclotomic
ring over `ℤ`, every `p²`-th power is congruent to a rational integer mod `p²`. -/
theorem exists_int_pow_p_sq_sub_dvd {A : Type*} [CommRing A] [IsCyclotomicExtension {p} ℤ A]
    (w : A) : ∃ n : ℤ, (p : A) ^ 2 ∣ w ^ p ^ 2 - (n : A) := by
  obtain ⟨a, ha⟩ := exists_int_sub_pow_prime_dvd (p := p) w
  rw [mem_span_singleton] at ha
  refine ⟨a ^ p, ?_⟩
  have h2 := dvd_sub_pow_of_dvd_sub (R := A) (a := w ^ p) (b := (a : A)) (p := p) ha 1
  have he : (w ^ p) ^ p ^ 1 = w ^ p ^ 2 := by
    rw [← pow_mul]
    ring_nf
  have he2 : ((a : A)) ^ p ^ 1 = ((a ^ p : ℤ) : A) := by
    push_cast
    rw [pow_one]
  rwa [he, he2, show (1 : ℕ) + 1 = 2 from rfl] at h2

end FltVandiver.Descent92
