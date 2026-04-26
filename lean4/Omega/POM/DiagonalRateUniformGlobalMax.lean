import Omega.POM.DiagonalRateSchurConcavity

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-uniform-global-max`. -/
theorem paper_pom_diagonal_rate_uniform_global_max {n : Nat} (δ : Real) (hn : 2 <= n)
    (hδ0 : 0 <= δ) (hδ1 : δ <= 1) {w : Fin n -> Real} (hw : Omega.POM.IsProbabilityVector w) :
    Omega.POM.pomDiagonalRate w δ <=
      Omega.POM.pomDiagonalRate (fun _ : Fin n => (1 : Real) / n) δ := by
  rcases hw with ⟨hw_nonneg, hw_sum⟩
  have hn_nat_pos : 0 < n := by omega
  have hnR_pos : (0 : Real) < n := by exact_mod_cast hn_nat_pos
  have hnR_ne : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn_nat_pos)
  have hunif_nonneg : ∀ i : Fin n, 0 ≤ (fun _ : Fin n => (1 : Real) / n) i := by
    intro i
    exact div_nonneg zero_le_one hnR_pos.le
  have hunif_sum : ∑ i : Fin n, (fun _ : Fin n => (1 : Real) / n) i = 1 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hnR_ne]
  have hunif_prob : IsProbabilityVector (fun _ : Fin n => (1 : Real) / n) := by
    exact ⟨hunif_nonneg, hunif_sum⟩
  have hcs :
      (∑ i : Fin n, w i) ^ (2 : ℕ) ≤ (n : Real) * ∑ i : Fin n, (w i) ^ (2 : ℕ) := by
    simpa [Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := w))
  have hquad_mul : (1 : Real) ≤ (n : Real) * ∑ i : Fin n, (w i) ^ (2 : ℕ) := by
    simpa [hw_sum] using hcs
  have hquad :
      (1 : Real) / n ≤ ∑ i : Fin n, (w i) ^ (2 : ℕ) := by
    exact (div_le_iff₀ hnR_pos).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hquad_mul)
  have hunif_sq :
      ∑ i : Fin n, ((fun _ : Fin n => (1 : Real) / n) i) ^ (2 : ℕ) = (1 : Real) / n := by
    calc
      ∑ i : Fin n, ((fun _ : Fin n => (1 : Real) / n) i) ^ (2 : ℕ)
          = (n : Real) * (((1 : Real) / n) ^ (2 : ℕ)) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (1 : Real) / n := by
            field_simp [hnR_ne]
  have hunif_sq_le :
      ∑ i : Fin n, ((fun _ : Fin n => (1 : Real) / n) i) ^ (2 : ℕ) ≤
        ∑ i : Fin n, (w i) ^ (2 : ℕ) := by
    rw [hunif_sq]
    exact hquad
  have hmajor : Majorizes w (fun _ : Fin n => (1 : Real) / n) := by
    refine ⟨?_, ?_⟩
    · rw [hunif_sum, hw_sum]
    · exact hunif_sq_le
  exact paper_pom_diagonal_rate_schur_concavity δ hδ0 hδ1 hunif_prob ⟨hw_nonneg, hw_sum⟩ hmajor

end Omega.POM
