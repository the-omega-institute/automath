import Mathlib.Tactic

namespace Omega.Zeta

/-- Zeroth Toeplitz coefficient from the low-order logarithmic jet. -/
def xi_jet_low_order_inequalities_toeplitz_c0 (ℓ1 : ℝ) : ℝ :=
  -ℓ1

/-- First Toeplitz coefficient from the low-order logarithmic jet. -/
def xi_jet_low_order_inequalities_toeplitz_c1 (ℓ2 : ℝ) : ℝ :=
  -ℓ2

/-- Second Toeplitz coefficient from the low-order logarithmic jet. -/
def xi_jet_low_order_inequalities_toeplitz_c2 (ℓ2 ℓ3 : ℝ) : ℝ :=
  ℓ2 - ℓ3

/-- The `1 × 1` leading Toeplitz minor. -/
def xi_jet_low_order_inequalities_minor_one (ℓ1 : ℝ) : ℝ :=
  xi_jet_low_order_inequalities_toeplitz_c0 ℓ1

/-- The leading `2 × 2` Toeplitz minor. -/
def xi_jet_low_order_inequalities_minor_two (ℓ1 ℓ2 : ℝ) : ℝ :=
  xi_jet_low_order_inequalities_toeplitz_c0 ℓ1 ^ 2 -
    xi_jet_low_order_inequalities_toeplitz_c1 ℓ2 ^ 2

/-- The selected endpoint `2 × 2` principal minor using coefficients `c₀` and `c₂`. -/
def xi_jet_low_order_inequalities_minor_endpoint_two (ℓ1 ℓ2 ℓ3 : ℝ) : ℝ :=
  xi_jet_low_order_inequalities_toeplitz_c0 ℓ1 ^ 2 -
    xi_jet_low_order_inequalities_toeplitz_c2 ℓ2 ℓ3 ^ 2

/-- The `3 × 3` symmetric Toeplitz determinant in coefficients `c₀,c₁,c₂`. -/
def xi_jet_low_order_inequalities_minor_three (ℓ1 ℓ2 ℓ3 : ℝ) : ℝ :=
  let c0 := xi_jet_low_order_inequalities_toeplitz_c0 ℓ1
  let c1 := xi_jet_low_order_inequalities_toeplitz_c1 ℓ2
  let c2 := xi_jet_low_order_inequalities_toeplitz_c2 ℓ2 ℓ3
  c0 ^ 3 - 2 * c0 * c1 ^ 2 + 2 * c1 ^ 2 * c2 - c0 * c2 ^ 2

/-- The displayed factorization of the `3 × 3` Toeplitz determinant. -/
def xi_jet_low_order_inequalities_minor_three_factor (ℓ1 ℓ2 ℓ3 : ℝ) : ℝ :=
  let c0 := xi_jet_low_order_inequalities_toeplitz_c0 ℓ1
  let c1 := xi_jet_low_order_inequalities_toeplitz_c1 ℓ2
  let c2 := xi_jet_low_order_inequalities_toeplitz_c2 ℓ2 ℓ3
  (c0 - c2) * (c0 ^ 2 + c0 * c2 - 2 * c1 ^ 2)

/-- Concrete low-order Toeplitz minor identities and their scalar nonnegativity rewrites. -/
def xi_jet_low_order_inequalities_statement (ℓ1 ℓ2 ℓ3 : ℝ) : Prop :=
  xi_jet_low_order_inequalities_minor_one ℓ1 = -ℓ1 ∧
    xi_jet_low_order_inequalities_minor_two ℓ1 ℓ2 = ℓ1 ^ 2 - ℓ2 ^ 2 ∧
    xi_jet_low_order_inequalities_minor_endpoint_two ℓ1 ℓ2 ℓ3 =
      ℓ1 ^ 2 - (ℓ2 - ℓ3) ^ 2 ∧
    xi_jet_low_order_inequalities_minor_three ℓ1 ℓ2 ℓ3 =
      xi_jet_low_order_inequalities_minor_three_factor ℓ1 ℓ2 ℓ3 ∧
    (0 ≤ xi_jet_low_order_inequalities_minor_one ℓ1 ↔ ℓ1 ≤ 0) ∧
    (0 ≤ xi_jet_low_order_inequalities_minor_two ℓ1 ℓ2 ↔ ℓ2 ^ 2 ≤ ℓ1 ^ 2) ∧
    (0 ≤ xi_jet_low_order_inequalities_minor_endpoint_two ℓ1 ℓ2 ℓ3 ↔
      (ℓ2 - ℓ3) ^ 2 ≤ ℓ1 ^ 2)

/-- Paper label: `cor:xi-jet-low-order-inequalities`. -/
theorem paper_xi_jet_low_order_inequalities (ℓ1 ℓ2 ℓ3 : ℝ) :
    xi_jet_low_order_inequalities_statement ℓ1 ℓ2 ℓ3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [xi_jet_low_order_inequalities_minor_one,
      xi_jet_low_order_inequalities_toeplitz_c0]
  · simp [xi_jet_low_order_inequalities_minor_two,
      xi_jet_low_order_inequalities_toeplitz_c0,
      xi_jet_low_order_inequalities_toeplitz_c1]
  · simp [xi_jet_low_order_inequalities_minor_endpoint_two,
      xi_jet_low_order_inequalities_toeplitz_c0,
      xi_jet_low_order_inequalities_toeplitz_c2]
  · unfold xi_jet_low_order_inequalities_minor_three
      xi_jet_low_order_inequalities_minor_three_factor
      xi_jet_low_order_inequalities_toeplitz_c0
      xi_jet_low_order_inequalities_toeplitz_c1
      xi_jet_low_order_inequalities_toeplitz_c2
    ring
  · simp [xi_jet_low_order_inequalities_minor_one,
      xi_jet_low_order_inequalities_toeplitz_c0]
  · simp [xi_jet_low_order_inequalities_minor_two,
      xi_jet_low_order_inequalities_toeplitz_c0,
      xi_jet_low_order_inequalities_toeplitz_c1]
  · simp [xi_jet_low_order_inequalities_minor_endpoint_two,
      xi_jet_low_order_inequalities_toeplitz_c0,
      xi_jet_low_order_inequalities_toeplitz_c2]

end Omega.Zeta
