import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete codimension-one residual-kernel data for a rank-one projection formula.

The scale is derived as `1 + normalizer ^ 2`, so positivity is a theorem of the package rather
than a stored abstract hypothesis. -/
structure xi_basepoint_scan_residual_kernel_codim1_rankone_Data where
  feature : ℝ → ℝ
  normalizer : ℝ

def xi_basepoint_scan_residual_kernel_codim1_rankone_Data.scale
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) : ℝ :=
  1 + D.normalizer ^ (2 : ℕ)

noncomputable def xi_basepoint_scan_residual_kernel_codim1_rankone_Data.residualKernel
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) (x y : ℝ) : ℝ :=
  D.feature x * (D.feature y / D.scale)

noncomputable def xi_basepoint_scan_residual_kernel_codim1_rankone_Data.leverage
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) (x : ℝ) : ℝ :=
  D.residualKernel x x

def xi_basepoint_scan_residual_kernel_codim1_rankone_Data.closedForm
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) : Prop :=
  ∀ x y, D.residualKernel x y = D.feature x * (D.feature y / D.scale)

def xi_basepoint_scan_residual_kernel_codim1_rankone_Data.rankOne
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) : Prop :=
  ∃ left right : ℝ → ℝ, ∀ x y, D.residualKernel x y = left x * right y

def xi_basepoint_scan_residual_kernel_codim1_rankone_Data.positiveKernel
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) : Prop :=
  ∀ x, 0 ≤ D.residualKernel x x

def xi_basepoint_scan_residual_kernel_codim1_rankone_Data.diagonalLeverage
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) : Prop :=
  ∀ x, D.leverage x = D.residualKernel x x

lemma xi_basepoint_scan_residual_kernel_codim1_rankone_scale_pos
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) :
    0 < D.scale := by
  dsimp [xi_basepoint_scan_residual_kernel_codim1_rankone_Data.scale]
  nlinarith [sq_nonneg D.normalizer]

/-- Paper label: `prop:xi-basepoint-scan-residual-kernel-codim1-rankone`. -/
theorem paper_xi_basepoint_scan_residual_kernel_codim1_rankone
    (D : xi_basepoint_scan_residual_kernel_codim1_rankone_Data) :
    D.closedForm ∧ D.rankOne ∧ D.positiveKernel ∧ D.diagonalLeverage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    rfl
  · refine ⟨D.feature, fun y => D.feature y / D.scale, ?_⟩
    intro x y
    rfl
  · intro x
    have hscale_nonneg : 0 ≤ D.scale :=
      (xi_basepoint_scan_residual_kernel_codim1_rankone_scale_pos D).le
    have hsq : 0 ≤ D.feature x * D.feature x := mul_self_nonneg (D.feature x)
    simpa [xi_basepoint_scan_residual_kernel_codim1_rankone_Data.residualKernel,
      mul_div_assoc] using div_nonneg hsq hscale_nonneg
  · intro x
    rfl

end Omega.Zeta
