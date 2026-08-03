import FltVandiver.Descent92Minimal
open CyclotomicNT

/-!
# Descent92, file 9 of 9 — the infinite descent

The measure (number of distinct prime ideal factors of `ξ`).  The strict decrease
and the infinite descent now live in the 9.5 route (`Descent95.descent_step_95`,
`Descent95.no_situation_95`); the exact-depth driver is retired.
-/

namespace FltVandiver.Descent92

open scoped NumberField nonZeroDivisors
open NumberField NumberField.IsCMField Polynomial UniqueFactorizationMonoid

variable {p : ℕ} [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]
  [NumberField.IsCMField (CyclotomicField p ℚ)]

/-- The descent measure: the number of distinct prime ideal factors of `ξ`. -/
noncomputable def meas {ζ : CyclotomicField p ℚ} {hζ : IsPrimitiveRoot ζ p}
    (S : Situation92 hζ) : ℕ :=
  (normalizedFactors (Ideal.span ({S.ξ} : Set (𝓞 (CyclotomicField p ℚ))))).toFinset.card

end FltVandiver.Descent92
