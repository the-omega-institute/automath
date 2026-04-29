import Mathlib.Tactic
import Omega.Folding.KilloZGDirichletMatrixEuler

namespace Omega.Zeta

/-- The continuant-compressed scalar sequence obtained from the existing two-state ZG Euler data. -/
def xi_time_part62b_zg_matrix_euler_continuant_D (n : ℕ) : ℚ :=
  Omega.Folding.zgDirichletEulerPartial n

/-- The nonautonomous continuant coefficient extracted from the `A_n, B_n` two-state transfer:
`D_n = D_{n-1} + c_n D_{n-2}` with `c_n = B_n / A_{n-1}`. -/
def xi_time_part62b_zg_matrix_euler_continuant_coeff (n : ℕ) : ℚ :=
  Omega.Folding.zgStateB (n + 2) / Omega.Folding.zgStateA (n + 1)

private theorem xi_time_part62b_zg_matrix_euler_continuant_D_closed (n : ℕ) :
    xi_time_part62b_zg_matrix_euler_continuant_D n = 2 - (1 / 2 : ℚ) ^ (n + 1) := by
  simpa [xi_time_part62b_zg_matrix_euler_continuant_D] using
    (Omega.Folding.paper_killo_zg_dirichlet_matrix_euler.2.2.1 n)

private theorem xi_time_part62b_zg_matrix_euler_continuant_A_closed (n : ℕ) :
    Omega.Folding.zgStateA n = 2 - (1 / 2 : ℚ) ^ n := by
  rfl

/-- Paper label: `thm:xi-time-part62b-zg-matrix-euler-continuant`. The existing ZG matrix-Euler
package already gives the two-state coordinates `A_n, B_n` and their closed form. Writing
`D_n := A_n + B_n` compresses the recursion to a scalar continuant law with an explicit
nonautonomous coefficient sequence, and the same closed form yields convergence to the ZG limit
value `2`. -/
theorem paper_xi_time_part62b_zg_matrix_euler_continuant :
    xi_time_part62b_zg_matrix_euler_continuant_D 0 = (3 / 2 : ℚ) ∧
      xi_time_part62b_zg_matrix_euler_continuant_D 1 = (7 / 4 : ℚ) ∧
      (∀ n : ℕ,
        xi_time_part62b_zg_matrix_euler_continuant_D (n + 2) =
          xi_time_part62b_zg_matrix_euler_continuant_D (n + 1) +
            xi_time_part62b_zg_matrix_euler_continuant_coeff n *
              xi_time_part62b_zg_matrix_euler_continuant_D n) ∧
      (∃ L : ℚ, L = 2 ∧
        ∀ n : ℕ, |xi_time_part62b_zg_matrix_euler_continuant_D n - L| = (1 / 2 : ℚ) ^ (n + 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [xi_time_part62b_zg_matrix_euler_continuant_D_closed]
    norm_num
  · rw [xi_time_part62b_zg_matrix_euler_continuant_D_closed]
    norm_num
  · intro n
    unfold xi_time_part62b_zg_matrix_euler_continuant_D
      xi_time_part62b_zg_matrix_euler_continuant_coeff
    unfold Omega.Folding.zgDirichletEulerPartial Omega.Folding.zgStateA Omega.Folding.zgStateB
    have hA_ne : (2 - (1 / 2 : ℚ) ^ (n + 1)) ≠ 0 := by
      have hpow_le_one : (1 / 2 : ℚ) ^ (n + 1) ≤ 1 := by
        exact pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℚ) ≤ 1)
      have hA_pos : 0 < 2 - (1 / 2 : ℚ) ^ (n + 1) := by
        linarith
      exact ne_of_gt hA_pos
    field_simp [hA_ne]
    ring_nf
  · refine ⟨2, rfl, ?_⟩
    intro n
    simpa [xi_time_part62b_zg_matrix_euler_continuant_D] using
      (Omega.Folding.paper_killo_zg_dirichlet_matrix_euler.2.2.2 n)

end Omega.Zeta
