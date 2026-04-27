import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part63-schur-crt-exact-recovery`. -/
theorem paper_xi_time_part63_schur_crt_exact_recovery {ι : Type*} [Fintype ι]
    (s t : ι → ℤ) (Q B : ℤ) (hQpos : 0 < Q)
    (hBoundS : ∀ i, -B ≤ s i ∧ s i ≤ B) (hBoundT : ∀ i, -B ≤ t i ∧ t i ≤ B)
    (hBig : 2 * B < Q) (hCong : ∀ i, ∃ k : ℤ, t i - s i = k * Q) :
    t = s := by
  funext i
  rcases hCong i with ⟨k, hk⟩
  have hupper : t i - s i ≤ 2 * B := by
    linarith [(hBoundT i).2, (hBoundS i).1]
  have hlower : -(2 * B) ≤ t i - s i := by
    linarith [(hBoundT i).1, (hBoundS i).2]
  by_cases hkzero : k = 0
  · rw [hkzero] at hk
    linarith
  · by_cases hkpos : 0 < k
    · have hone_le_k : (1 : ℤ) ≤ k := by
        omega
      have hQ_le_kQ : Q ≤ k * Q := by
        calc
          Q = (1 : ℤ) * Q := by ring
          _ ≤ k * Q := mul_le_mul_of_nonneg_right hone_le_k (le_of_lt hQpos)
      have hQ_le_twoB : Q ≤ 2 * B := by
        linarith [hQ_le_kQ, hupper, hk]
      linarith
    · have hk_le_neg_one : k ≤ -1 := by
        omega
      have hkQ_le_negQ : k * Q ≤ -Q := by
        calc
          k * Q ≤ (-1 : ℤ) * Q :=
            mul_le_mul_of_nonneg_right hk_le_neg_one (le_of_lt hQpos)
          _ = -Q := by ring
      have hQ_le_twoB : Q ≤ 2 * B := by
        linarith [hlower, hkQ_le_negQ, hk]
      linarith

end Omega.Zeta
