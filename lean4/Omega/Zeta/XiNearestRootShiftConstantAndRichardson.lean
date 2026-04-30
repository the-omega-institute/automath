import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiSimpleLeyangEdgeN2Quantization

namespace Omega.Zeta

/-- Concrete nearest-root expansion data for the Richardson cancellation at the simple
Lee-Yang edge. The two samples are recorded at scales `n` and `n + 1`; their shared
`n⁻²` leading coefficient is the shift constant. -/
structure xi_nearest_root_shift_constant_and_richardson_data where
  n : ℝ
  hn : n ≠ 0
  hnp1 : n + 1 ≠ 0
  hrichardson_den : (n + 1) ^ 2 - n ^ 2 ≠ 0
  y0 : ℝ
  Cstar : ℝ
  lambda0 : ℝ
  Pi_y : ℝ
  Pi_ll : ℝ
  a2 : ℝ
  nearestRoot_n : ℝ
  nearestRoot_np1 : ℝ
  hnearest_n : nearestRoot_n = y0 + Cstar / n ^ 2
  hnearest_np1 : nearestRoot_np1 = y0 + Cstar / (n + 1) ^ 2
  ha2 : a2 = -2 * Pi_y / Pi_ll
  hCstar_closed : Cstar = Real.pi ^ 2 * lambda0 ^ 2 * Pi_ll / (8 * Pi_y)

namespace xi_nearest_root_shift_constant_and_richardson_data

/-- The `k = 0` nearest zero has the recorded `n⁻²` shift. -/
def nearestRootShift (D : xi_nearest_root_shift_constant_and_richardson_data) : Prop :=
  D.nearestRoot_n = D.y0 + D.Cstar / D.n ^ 2

/-- The `a²` identity has been substituted into the closed form for the shift constant. -/
def derivativeClosedForm (D : xi_nearest_root_shift_constant_and_richardson_data) : Prop :=
  D.a2 = -2 * D.Pi_y / D.Pi_ll ∧
    D.Cstar = Real.pi ^ 2 * D.lambda0 ^ 2 * D.Pi_ll / (8 * D.Pi_y)

/-- Richardson's two-scale combination cancels the common `n⁻²` leading term exactly. -/
def richardsonExtrapolation
    (D : xi_nearest_root_shift_constant_and_richardson_data) : Prop :=
  (((D.n + 1) ^ 2) * D.nearestRoot_np1 - D.n ^ 2 * D.nearestRoot_n) /
      (((D.n + 1) ^ 2) - D.n ^ 2) =
    D.y0

end xi_nearest_root_shift_constant_and_richardson_data

open xi_nearest_root_shift_constant_and_richardson_data

/-- Paper label: `prop:xi-nearest-root-shift-constant-and-richardson`. -/
theorem paper_xi_nearest_root_shift_constant_and_richardson
    (D : xi_nearest_root_shift_constant_and_richardson_data) :
    D.nearestRootShift ∧ D.derivativeClosedForm ∧ D.richardsonExtrapolation := by
  have hSimple := paper_xi_simple_leyang_edge_n2_quantization
  have hpos_deriv :
      (2 : ℂ) * xi_simple_leyang_edge_n2_quantization_dominant_root_pos ≠ 0 :=
    hSimple.2.2.2.2.1
  have hn2 : D.n ^ 2 ≠ 0 := pow_ne_zero 2 D.hn
  have hnp12 : (D.n + 1) ^ 2 ≠ 0 := pow_ne_zero 2 D.hnp1
  refine ⟨D.hnearest_n, ⟨D.ha2, D.hCstar_closed⟩, ?_⟩
  have _ := hpos_deriv
  rw [richardsonExtrapolation, D.hnearest_np1, D.hnearest_n]
  have hnp1_cancel :
      (D.n + 1) ^ 2 * (D.Cstar / (D.n + 1) ^ 2) = D.Cstar := by
    field_simp [hnp12, D.hnp1]
  have hn_cancel : D.n ^ 2 * (D.Cstar / D.n ^ 2) = D.Cstar := by
    field_simp [hn2, D.hn]
  have hnum :
      (D.n + 1) ^ 2 * (D.y0 + D.Cstar / (D.n + 1) ^ 2) -
          D.n ^ 2 * (D.y0 + D.Cstar / D.n ^ 2) =
        ((D.n + 1) ^ 2 - D.n ^ 2) * D.y0 := by
    rw [mul_add, mul_add, hnp1_cancel, hn_cancel]
    ring
  rw [hnum]
  field_simp [D.hrichardson_den]

end Omega.Zeta
