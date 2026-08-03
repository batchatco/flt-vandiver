/-!
# Precompiled certificate kernel: modular exponentiation

The single arithmetic primitive shared by the fast (`Fermat`-reduced) `Q_i`
certificate evaluation (`FltVandiver.QiCertFast`): binary square-and-multiply
modular exponentiation over `Nat`.  Precompiled (see `lakefile.toml`) so
`native_decide` certificate runs call optimized code.

Soundness: `powModK_spec` in `FltVandiver.QiCertFast` proves
`powModK b m e = b ^ e % m`.
-/

namespace CertKernel

/-- Modular exponentiation (square-and-multiply). -/
def powModK (b m : Nat) : Nat → Nat
  | 0 => 1 % m
  | (e + 1) =>
    let h := powModK b m ((e + 1) / 2)
    let h2 := h * h % m
    if (e + 1) % 2 = 1 then h2 * (b % m) % m else h2
decreasing_by exact Nat.div_lt_self (Nat.succ_pos e) Nat.one_lt_two

end CertKernel
