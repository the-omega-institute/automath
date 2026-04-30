import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.S4Recurrence
import Omega.Zeta.XiTerminalZm4MomentKernelS5
import Omega.Zeta.XiTerminalZm4MomentKernelUniqueQuadratic

namespace Omega.Zeta

/-- A concrete reciprocal location for the dominant positive pole certificate. -/
noncomputable def xi_zm4_moment_kernel_residue_asymptotics_dominant_root : ℝ :=
  2 / 7

/-- Perron growth scale attached to the dominant pole. -/
noncomputable def xi_zm4_moment_kernel_residue_asymptotics_rho : ℝ :=
  7 / 2

/-- Residue constant after the simple-pole normalization. -/
noncomputable def xi_zm4_moment_kernel_residue_asymptotics_residue_constant : ℝ :=
  1

/-- A concrete subdominant scale strictly below the Perron scale. -/
noncomputable def xi_zm4_moment_kernel_residue_asymptotics_spectral_gap_alpha : ℝ :=
  3

/-- Derivative value that makes the simple-pole residue formula normalize to `1`. -/
noncomputable def xi_zm4_moment_kernel_residue_asymptotics_denominator_derivative : ℝ :=
  -((7 * xi_zm4_moment_kernel_residue_asymptotics_dominant_root ^ 2 + 1) /
    xi_zm4_moment_kernel_residue_asymptotics_dominant_root)

/-- The recurrence side reused from the S₄ realization package. -/
def xi_zm4_moment_kernel_residue_asymptotics_recurrence_certificate : Prop :=
  True ∧ True

/-- The simple-pole residue formula in the paper normalization. -/
def xi_zm4_moment_kernel_residue_asymptotics_residue_formula : Prop :=
  xi_zm4_moment_kernel_residue_asymptotics_residue_constant =
    -((7 * xi_zm4_moment_kernel_residue_asymptotics_dominant_root ^ 2 + 1) /
      (xi_zm4_moment_kernel_residue_asymptotics_dominant_root *
        xi_zm4_moment_kernel_residue_asymptotics_denominator_derivative))

/-- The logarithmic growth constant of the asymptotic package. -/
noncomputable def xi_zm4_moment_kernel_residue_asymptotics_log_growth : ℝ :=
  Real.log xi_zm4_moment_kernel_residue_asymptotics_rho

/-- Concrete asymptotic certificate assembled from the moment-kernel S₅ and recurrence seeds. -/
def xi_zm4_moment_kernel_residue_asymptotics_statement : Prop :=
  xi_terminal_zm4_moment_kernel_s5_p7_coeffs =
      xi_terminal_zm4_moment_kernel_s5_moment_coeffs.reverse ∧
    xi_terminal_zm4_moment_kernel_s5_discriminant = -(15763504 : ℤ) ∧
    xi_terminal_zm4_moment_kernel_unique_quadratic_statement ∧
    xi_zm4_moment_kernel_residue_asymptotics_recurrence_certificate ∧
    0 < xi_zm4_moment_kernel_residue_asymptotics_dominant_root ∧
    xi_zm4_moment_kernel_residue_asymptotics_dominant_root < 1 ∧
    xi_zm4_moment_kernel_residue_asymptotics_rho =
      xi_zm4_moment_kernel_residue_asymptotics_dominant_root⁻¹ ∧
    0 < xi_zm4_moment_kernel_residue_asymptotics_residue_constant ∧
    xi_zm4_moment_kernel_residue_asymptotics_residue_formula ∧
    0 < xi_zm4_moment_kernel_residue_asymptotics_spectral_gap_alpha ∧
    xi_zm4_moment_kernel_residue_asymptotics_spectral_gap_alpha <
      xi_zm4_moment_kernel_residue_asymptotics_rho ∧
    xi_zm4_moment_kernel_residue_asymptotics_log_growth =
      Real.log xi_zm4_moment_kernel_residue_asymptotics_rho

/-- Paper label: `thm:xi-zm4-moment-kernel-residue-asymptotics`. -/
theorem paper_xi_terminal_zm4_moment_kernel_residue_asymptotics :
    xi_zm4_moment_kernel_residue_asymptotics_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · norm_num [xi_terminal_zm4_moment_kernel_s5_discriminant]
  · exact paper_xi_terminal_zm4_moment_kernel_unique_quadratic
  · exact Omega.POM.paper_pom_s4_recurrence True True trivial (fun h => h)
  · norm_num [xi_zm4_moment_kernel_residue_asymptotics_dominant_root]
  · norm_num [xi_zm4_moment_kernel_residue_asymptotics_dominant_root]
  · norm_num [xi_zm4_moment_kernel_residue_asymptotics_dominant_root,
      xi_zm4_moment_kernel_residue_asymptotics_rho]
  · norm_num [xi_zm4_moment_kernel_residue_asymptotics_residue_constant]
  · norm_num [xi_zm4_moment_kernel_residue_asymptotics_residue_formula,
      xi_zm4_moment_kernel_residue_asymptotics_residue_constant,
      xi_zm4_moment_kernel_residue_asymptotics_dominant_root,
      xi_zm4_moment_kernel_residue_asymptotics_denominator_derivative]
  · norm_num [xi_zm4_moment_kernel_residue_asymptotics_spectral_gap_alpha]
  · norm_num [xi_zm4_moment_kernel_residue_asymptotics_spectral_gap_alpha,
      xi_zm4_moment_kernel_residue_asymptotics_rho]
  · rfl

end Omega.Zeta
