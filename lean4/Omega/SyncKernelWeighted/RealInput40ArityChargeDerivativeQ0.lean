import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The `q = 0` specialization `P₇(Λ, 0) = Λ² (Λ - 1) (Λ⁴ - Λ³ - 1)`. -/
def realInput40ArityChargeP7Q0 (Λ : ℝ) : ℝ :=
  Λ ^ 2 * (Λ - 1) * (Λ ^ 4 - Λ ^ 3 - 1)

/-- The `Λ`-derivative of the `q = 0` specialization evaluated symbolically at `Λ`.  At a root of
`Λ⁴ - Λ³ - 1`, the product rule collapses to the simple factor used in the proof below. -/
def realInput40ArityChargeP7LambdaPartialAtQ0 (Λ : ℝ) : ℝ :=
  Λ ^ 2 * (Λ - 1) * (4 * Λ ^ 3 - 3 * Λ ^ 2)

/-- The `q`-derivative of `P₇` at `q = 0`, written in the factorized form needed for the implicit
derivative computation. -/
def realInput40ArityChargeP7QPartialAtQ0 (Λ : ℝ) : ℝ :=
  -(Λ ^ 3 * (Λ - 1) * (2 * Λ ^ 3 + Λ ^ 2 + 8 * Λ - 2))

/-- The implicit slope `-∂q P₇ / ∂Λ P₇` at the zero-charge root. -/
noncomputable def realInput40ArityChargeImplicitSlopeQ0 (κ : ℝ) : ℝ :=
  -realInput40ArityChargeP7QPartialAtQ0 κ / realInput40ArityChargeP7LambdaPartialAtQ0 κ

/-- If `κ > 1` is the real root of `κ⁴ - κ³ - 1 = 0`, then the `q = 0` specialization factors as
claimed, the root is simple on that slice, and the implicit derivative simplifies to the explicit
closed form from the paper.
    prop:real-input-40-arity-charge-derivative-q0 -/
theorem paper_real_input_40_arity_charge_derivative_q0
    {κ : ℝ} (hκroot : κ ^ 4 - κ ^ 3 - 1 = 0) (hκgt : 1 < κ) :
    realInput40ArityChargeP7Q0 κ = 0 ∧
      realInput40ArityChargeP7LambdaPartialAtQ0 κ ≠ 0 ∧
      realInput40ArityChargeImplicitSlopeQ0 κ =
        (2 * κ ^ 3 + κ ^ 2 + 8 * κ - 2) / (κ * (4 * κ - 3)) := by
  have hκpos : 0 < κ := by linarith
  have hκne : κ ≠ 0 := ne_of_gt hκpos
  have hκ1ne : κ - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hκgt)
  have h4κ3pos : 0 < 4 * κ - 3 := by linarith
  have h4κ3ne : 4 * κ - 3 ≠ 0 := ne_of_gt h4κ3pos
  refine ⟨?_, ?_, ?_⟩
  · unfold realInput40ArityChargeP7Q0
    nlinarith [hκroot]
  · unfold realInput40ArityChargeP7LambdaPartialAtQ0
    have hrepr : κ ^ 2 * (κ - 1) * (4 * κ ^ 3 - 3 * κ ^ 2) = κ ^ 4 * (κ - 1) * (4 * κ - 3) := by
      ring
    rw [hrepr]
    positivity
  · unfold realInput40ArityChargeImplicitSlopeQ0 realInput40ArityChargeP7QPartialAtQ0
      realInput40ArityChargeP7LambdaPartialAtQ0
    field_simp [hκne, hκ1ne, h4κ3ne]

end Omega.SyncKernelWeighted
