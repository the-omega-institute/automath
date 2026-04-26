import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

noncomputable section

/-- The concrete `2 × 2` real matrix model for the `B₃` sector-frame package. -/
abbrev xi_horizon_b3_sector_frame_decomposition_matrix := Matrix (Fin 2) (Fin 2) ℝ

/-- The projector onto the distinguished parallel axis. -/
def xi_horizon_b3_sector_frame_decomposition_parallelProjector :
    xi_horizon_b3_sector_frame_decomposition_matrix :=
  !![(1 : ℝ), 0; 0, 0]

/-- The projector onto the perpendicular axis. -/
def xi_horizon_b3_sector_frame_decomposition_perpendicularProjector :
    xi_horizon_b3_sector_frame_decomposition_matrix :=
  !![(0 : ℝ), 0; 0, 1]

/-- The first sector frame operator, supported on the parallel line. -/
def xi_horizon_b3_sector_frame_decomposition_sector0 :
    xi_horizon_b3_sector_frame_decomposition_matrix :=
  xi_horizon_b3_sector_frame_decomposition_parallelProjector

/-- The `+` sector frame operator. -/
def xi_horizon_b3_sector_frame_decomposition_sectorPlus :
    xi_horizon_b3_sector_frame_decomposition_matrix :=
  !![(1 : ℝ) / 2, (1 : ℝ) / 2; (1 : ℝ) / 2, (1 : ℝ) / 2]

/-- The `-` sector frame operator. -/
def xi_horizon_b3_sector_frame_decomposition_sectorMinus :
    xi_horizon_b3_sector_frame_decomposition_matrix :=
  !![(1 : ℝ) / 2, -(1 : ℝ) / 2; -(1 : ℝ) / 2, (1 : ℝ) / 2]

/-- The quadratic energy attached to a symmetric `2 × 2` matrix and a vector `(x,y)`. -/
def xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
    (M : xi_horizon_b3_sector_frame_decomposition_matrix) (x y : ℝ) : ℝ :=
  M 0 0 * x ^ 2 + (M 0 1 + M 1 0) * x * y + M 1 1 * y ^ 2

/-- Paper-facing statement for the explicit `B₃` sector-frame decomposition. -/
def xi_horizon_b3_sector_frame_decomposition_statement : Prop :=
  xi_horizon_b3_sector_frame_decomposition_sectorPlus +
      xi_horizon_b3_sector_frame_decomposition_sectorMinus =
    xi_horizon_b3_sector_frame_decomposition_parallelProjector +
      xi_horizon_b3_sector_frame_decomposition_perpendicularProjector ∧
    xi_horizon_b3_sector_frame_decomposition_sector0 +
        xi_horizon_b3_sector_frame_decomposition_sectorPlus +
        xi_horizon_b3_sector_frame_decomposition_sectorMinus =
      (2 : ℝ) • xi_horizon_b3_sector_frame_decomposition_parallelProjector +
        xi_horizon_b3_sector_frame_decomposition_perpendicularProjector ∧
    ∀ x y : ℝ,
      xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
          xi_horizon_b3_sector_frame_decomposition_sector0 x y =
        x ^ 2 ∧
        xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
            xi_horizon_b3_sector_frame_decomposition_sectorPlus x y =
          (x + y) ^ 2 / 2 ∧
        xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
            xi_horizon_b3_sector_frame_decomposition_sectorMinus x y =
          (x - y) ^ 2 / 2 ∧
        y ^ 2 =
          xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
              xi_horizon_b3_sector_frame_decomposition_sectorPlus x y +
            xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
              xi_horizon_b3_sector_frame_decomposition_sectorMinus x y -
            xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
              xi_horizon_b3_sector_frame_decomposition_sector0 x y ∧
        x ^ 2 + y ^ 2 =
          xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
              xi_horizon_b3_sector_frame_decomposition_sectorPlus x y +
            xi_horizon_b3_sector_frame_decomposition_quadraticEnergy
              xi_horizon_b3_sector_frame_decomposition_sectorMinus x y

/-- Paper label: `thm:xi-horizon-b3-sector-frame-decomposition`. The three explicit sector frame
operators split into the parallel and perpendicular projectors, and their quadratic energies
recover the parallel/perpendicular contributions by direct matrix expansion. -/
theorem paper_xi_horizon_b3_sector_frame_decomposition :
    xi_horizon_b3_sector_frame_decomposition_statement := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [xi_horizon_b3_sector_frame_decomposition_sectorPlus,
        xi_horizon_b3_sector_frame_decomposition_sectorMinus,
        xi_horizon_b3_sector_frame_decomposition_parallelProjector,
        xi_horizon_b3_sector_frame_decomposition_perpendicularProjector]
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [xi_horizon_b3_sector_frame_decomposition_sector0,
        xi_horizon_b3_sector_frame_decomposition_sectorPlus,
        xi_horizon_b3_sector_frame_decomposition_sectorMinus,
        xi_horizon_b3_sector_frame_decomposition_parallelProjector,
        xi_horizon_b3_sector_frame_decomposition_perpendicularProjector]
  · intro x y
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · norm_num [xi_horizon_b3_sector_frame_decomposition_quadraticEnergy,
        xi_horizon_b3_sector_frame_decomposition_sector0,
        xi_horizon_b3_sector_frame_decomposition_parallelProjector]
    · ring_nf
      norm_num [xi_horizon_b3_sector_frame_decomposition_quadraticEnergy,
        xi_horizon_b3_sector_frame_decomposition_sectorPlus]
      ring
    · ring_nf
      norm_num [xi_horizon_b3_sector_frame_decomposition_quadraticEnergy,
        xi_horizon_b3_sector_frame_decomposition_sectorMinus]
      ring
    · ring_nf
      norm_num [xi_horizon_b3_sector_frame_decomposition_quadraticEnergy,
        xi_horizon_b3_sector_frame_decomposition_sector0,
        xi_horizon_b3_sector_frame_decomposition_sectorPlus,
        xi_horizon_b3_sector_frame_decomposition_sectorMinus,
        xi_horizon_b3_sector_frame_decomposition_parallelProjector]
      ring
    · ring_nf
      norm_num [xi_horizon_b3_sector_frame_decomposition_quadraticEnergy,
        xi_horizon_b3_sector_frame_decomposition_sectorPlus,
        xi_horizon_b3_sector_frame_decomposition_sectorMinus]
      ring

end

end Omega.Zeta
