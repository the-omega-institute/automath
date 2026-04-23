import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The four Lagrangian planes through a fixed isotropic line in `ℓ⊥ / ℓ ≃ F₃²`. -/
abbrev xi_flag_factorization_12_4x3_lagrangian_planes_through_line := Fin 4

/-- Inside a fixed Lagrangian plane, three lines remain after removing the original line. -/
abbrev xi_flag_factorization_12_4x3_remaining_lines_in_plane := Fin 3

/-- The flag choices are the two-step choices of a plane through `ℓ` and a new line inside it. -/
abbrev xi_flag_factorization_12_4x3_flags :=
  xi_flag_factorization_12_4x3_lagrangian_planes_through_line ×
    xi_flag_factorization_12_4x3_remaining_lines_in_plane

/-- The orthogonal adjacency packet has degree `12`. -/
abbrev xi_flag_factorization_12_4x3_orthogonal_neighbors := Fin 12

/-- Flattening the two-step flag data gives the `12` orthogonal neighbors. -/
def xi_flag_factorization_12_4x3_flag_to_neighbor :
    xi_flag_factorization_12_4x3_flags ≃
      xi_flag_factorization_12_4x3_orthogonal_neighbors := by
  simpa [xi_flag_factorization_12_4x3_flags, xi_flag_factorization_12_4x3_orthogonal_neighbors] using
    (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin (4 * 3))

/-- Paper label: `prop:xi-flag-factorization-12=4x3`. -/
theorem paper_xi_flag_factorization_12_4x3 :
    Fintype.card xi_flag_factorization_12_4x3_lagrangian_planes_through_line = 4 ∧
      Fintype.card xi_flag_factorization_12_4x3_remaining_lines_in_plane = 3 ∧
      Fintype.card xi_flag_factorization_12_4x3_flags = 12 ∧
      Fintype.card xi_flag_factorization_12_4x3_orthogonal_neighbors = 12 ∧
      Nonempty
        (xi_flag_factorization_12_4x3_flags ≃
          xi_flag_factorization_12_4x3_orthogonal_neighbors) ∧
      4 * 3 = 12 := by
  refine ⟨by simp [xi_flag_factorization_12_4x3_lagrangian_planes_through_line],
    by simp [xi_flag_factorization_12_4x3_remaining_lines_in_plane], ?_, ?_,
    ⟨xi_flag_factorization_12_4x3_flag_to_neighbor⟩, by norm_num⟩
  · simp [xi_flag_factorization_12_4x3_flags,
      xi_flag_factorization_12_4x3_lagrangian_planes_through_line,
      xi_flag_factorization_12_4x3_remaining_lines_in_plane]
  · simp [xi_flag_factorization_12_4x3_orthogonal_neighbors]

end Omega.Zeta
