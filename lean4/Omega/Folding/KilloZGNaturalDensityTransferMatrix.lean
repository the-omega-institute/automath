import Omega.Folding.KilloZGDirichletMatrixEuler

namespace Omega.Folding

/-- Paper label: `thm:killo-zg-natural-density-transfer-matrix`. -/
theorem paper_killo_zg_natural_density_transfer_matrix :
    (∀ n, zgDirichletEulerPartial n = 2 - (1 / 2 : Rat) ^ (n + 1)) ∧
      (∀ n, zgDirichletEulerPartial n < 2) ∧
      (∀ n, zgDirichletEulerPartial n < zgDirichletEulerPartial (n + 1)) := by
  rcases paper_killo_zg_dirichlet_matrix_euler with ⟨_, _, hclosed, _⟩
  refine ⟨hclosed, ?_, ?_⟩
  · intro n
    rw [hclosed]
    have hpow_pos : (0 : Rat) < (1 / 2 : Rat) ^ (n + 1) := by
      positivity
    linarith
  · intro n
    rw [hclosed, hclosed (n + 1)]
    have hhalf_lt_one : (1 / 2 : Rat) < 1 := by
      norm_num
    have hpow_pos : (0 : Rat) < (1 / 2 : Rat) ^ (n + 1) := by
      positivity
    have hpow_lt :
        (1 / 2 : Rat) ^ (n + 2) < (1 / 2 : Rat) ^ (n + 1) := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      simpa using mul_lt_mul_of_pos_left hhalf_lt_one hpow_pos
    linarith

end Omega.Folding
