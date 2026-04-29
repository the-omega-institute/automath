import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete positive scaling factor for the Cauchy/cosh linearization picture. -/
structure xi_cauchy_cosh_unitary_linearization_data where
  m : ℝ
  m_pos : 0 < m

namespace xi_cauchy_cosh_unitary_linearization_data

/-- Weighted scaling operator on the Cauchy side. -/
def weightedScaling (D : xi_cauchy_cosh_unitary_linearization_data) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt D.m * f (x / D.m)

/-- The logarithmic chart on the positive real line. -/
def logChart (x : ℝ) : ℝ :=
  Real.log x

/-- Inverse logarithmic chart. -/
def logChartInv (y : ℝ) : ℝ :=
  Real.exp y

/-- The Cauchy-side scaling formula. -/
def unitaryScaling (D : xi_cauchy_cosh_unitary_linearization_data) : Prop :=
  ∀ f x, D.weightedScaling f x = Real.sqrt D.m * f (x / D.m)

/-- The logarithmic chart converts multiplicative distance into ordinary absolute difference. -/
def logChartIsometry (D : xi_cauchy_cosh_unitary_linearization_data) : Prop :=
  ∀ x y, 0 < x → 0 < y → |logChart x - logChart y| = |Real.log (x / y)|

/-- Conjugating positive scaling by the logarithmic chart turns it into translation by `-log m`. -/
def shiftIntertwining (D : xi_cauchy_cosh_unitary_linearization_data) : Prop :=
  ∀ x, 0 < x → logChart (x / D.m) = logChart x - Real.log D.m

end xi_cauchy_cosh_unitary_linearization_data

private lemma xi_cauchy_cosh_unitary_linearization_unitary_scaling_proof
    (D : xi_cauchy_cosh_unitary_linearization_data) : D.unitaryScaling := by
  intro f x
  rfl

private lemma xi_cauchy_cosh_unitary_linearization_log_chart_isometry_proof
    (D : xi_cauchy_cosh_unitary_linearization_data) : D.logChartIsometry := by
  intro x y hx hy
  rw [xi_cauchy_cosh_unitary_linearization_data.logChart, xi_cauchy_cosh_unitary_linearization_data.logChart,
    Real.log_div hx.ne' hy.ne']

private lemma xi_cauchy_cosh_unitary_linearization_shift_intertwining_proof
    (D : xi_cauchy_cosh_unitary_linearization_data) : D.shiftIntertwining := by
  intro x hx
  rw [xi_cauchy_cosh_unitary_linearization_data.logChart, xi_cauchy_cosh_unitary_linearization_data.logChart,
    Real.log_div hx.ne' D.m_pos.ne']

/-- Paper label: `thm:xi-cauchy-cosh-unitary-linearization`. The weighted Cauchy scaling has the
expected square-root prefactor, the logarithmic chart converts multiplicative distance to ordinary
absolute difference, and scaling by `m` becomes translation by `-log m`. -/
theorem paper_xi_cauchy_cosh_unitary_linearization (D : xi_cauchy_cosh_unitary_linearization_data) :
    D.unitaryScaling /\ D.logChartIsometry /\ D.shiftIntertwining := by
  exact ⟨xi_cauchy_cosh_unitary_linearization_unitary_scaling_proof D,
    xi_cauchy_cosh_unitary_linearization_log_chart_isometry_proof D,
    xi_cauchy_cosh_unitary_linearization_shift_intertwining_proof D⟩

end

end Omega.Zeta
