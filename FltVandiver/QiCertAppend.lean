import FltVandiver.QiCertificate

/-!
# Splitting the `Q_i` certificate over a list split

Relocated from the retired log-kernel engine; used to assemble sliced
certificates (`FLT16843Cert`). A leaf module so that slice assemblies do not
sit on the hot import path of the per-prime certificate files.
-/

namespace FltVandiver

theorem vandiverCert_append {p ℓ t : ℕ} [Fact ℓ.Prime] {L₁ L₂ : List ℕ}
    (h1 : QiCert.vandiverCert p ℓ t L₁ = true)
    (h2 : QiCert.vandiverCert p ℓ t L₂ = true) :
    QiCert.vandiverCert p ℓ t (L₁ ++ L₂) = true := by
  rw [QiCert.vandiverCert] at h1 h2 ⊢
  simp only [Bool.and_eq_true, List.all_append, List.all_eq_true] at h1 h2 ⊢
  exact ⟨h1.1, h1.2, h2.2⟩

/-- **Slice assembly**: a full-list certificate from `n` width-`w` slices.
Mirrors the manual `take`/`drop` chains of the sliced certificate files, once
and for all (the `p = 2124679` campaign has dozens of slices). -/
theorem vandiverCert_of_slices {p ℓ t : ℕ} [Fact ℓ.Prime] {L : List ℕ}
    {w n : ℕ} (hn : 0 < n) (hcover : L.length ≤ n * w)
    (h : ∀ j, j < n → QiCert.vandiverCert p ℓ t ((L.drop (j * w)).take w) = true) :
    QiCert.vandiverCert p ℓ t L = true := by
  have aux : ∀ j, 0 < j → j ≤ n →
      QiCert.vandiverCert p ℓ t (L.drop ((n - j) * w)) = true := by
    intro j
    induction j with
    | zero => omega
    | succ i ih =>
      intro _ hle
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have hmul : (n - 1) * w + w = n * w := by
          rw [← Nat.succ_mul]
          congr 1
          omega
        have hlen : (L.drop ((n - 1) * w)).length ≤ w := by
          rw [List.length_drop]
          omega
        have hj := h (n - 1) (by omega)
        rwa [List.take_of_length_le hlen] at hj
      · have hmul : (n - i) * w = (n - (i + 1)) * w + w := by
          rw [show n - i = (n - (i + 1)) + 1 from by omega, Nat.succ_mul]
        have hdd : (L.drop ((n - (i + 1)) * w)).drop w = L.drop ((n - i) * w) := by
          rw [List.drop_drop, hmul, Nat.add_comm]
        have hstep : L.drop ((n - (i + 1)) * w)
            = ((L.drop ((n - (i + 1)) * w)).take w)
              ++ L.drop ((n - i) * w) := by
          rw [← hdd]
          exact (List.take_append_drop w _).symm
        rw [hstep]
        exact vandiverCert_append (h (n - (i + 1)) (by omega)) (ih hi (by omega))
  have hfin := aux n hn le_rfl
  rwa [Nat.sub_self, Nat.zero_mul, List.drop_zero] at hfin

end FltVandiver
