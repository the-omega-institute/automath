import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete data for translating a frozen pressure ray to spectral radius and entropy formulas. -/
structure conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data where
  LambdaInfinity : ℝ

namespace conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data

/-- The saturated pressure ray. -/
noncomputable def conclusion_one_order_spectral_radius_saturation_freezes_all_orders_pressure
    (D : conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data) (q : ℕ) : ℝ :=
  Real.log 2 + (q - 1 : ℝ) * D.LambdaInfinity

/-- The spectral radius obtained by exponentiating the pressure. -/
noncomputable def conclusion_one_order_spectral_radius_saturation_freezes_all_orders_radius
    (D : conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data) (q : ℕ) : ℝ :=
  Real.exp
    (D.conclusion_one_order_spectral_radius_saturation_freezes_all_orders_pressure q)

/-- The entropy expression normalized from pressure. -/
noncomputable def conclusion_one_order_spectral_radius_saturation_freezes_all_orders_entropy
    (D : conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data) (q : ℕ) : ℝ :=
  (q : ℝ) * Real.log 2 -
    D.conclusion_one_order_spectral_radius_saturation_freezes_all_orders_pressure q

/-- Concrete statement: all orders satisfy the saturated radius and entropy identities. -/
def statement (D : conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data) :
    Prop :=
  ∀ q : ℕ,
    D.conclusion_one_order_spectral_radius_saturation_freezes_all_orders_radius q =
        2 * Real.exp ((q - 1 : ℝ) * D.LambdaInfinity) ∧
      D.conclusion_one_order_spectral_radius_saturation_freezes_all_orders_entropy q =
        (q - 1 : ℝ) * (Real.log 2 - D.LambdaInfinity)

end conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data

/-- Paper label: `cor:conclusion-one-order-spectral-radius-saturation-freezes-all-orders`. -/
theorem paper_conclusion_one_order_spectral_radius_saturation_freezes_all_orders
    (D : conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data) :
    D.statement := by
  intro q
  constructor
  · simp [
      conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data.conclusion_one_order_spectral_radius_saturation_freezes_all_orders_radius,
      conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data.conclusion_one_order_spectral_radius_saturation_freezes_all_orders_pressure,
      Real.exp_add, Real.exp_log]
  · simp [
      conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data.conclusion_one_order_spectral_radius_saturation_freezes_all_orders_entropy,
      conclusion_one_order_spectral_radius_saturation_freezes_all_orders_data.conclusion_one_order_spectral_radius_saturation_freezes_all_orders_pressure]
    ring

end Omega.Conclusion
