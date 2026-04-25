import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- The explicit degree-`7` determinant factor from the generated arity-charge audit. -/
def real_input_40_arity_charge_det_closed_Q7 (z q : ℚ) : ℚ :=
  1 - 2 * z + (1 - 5 * q) * z ^ 2 + 6 * q * z ^ 3 +
    (6 * q ^ 2 - 3 * q - 1) * z ^ 4 + (-4 * q ^ 2 - q + 1) * z ^ 5 +
    q * (4 * q - 3) * z ^ 6 + q * (1 - q) * z ^ 7

/-- The reciprocal degree-`7` spectral polynomial in the Perron variable `Λ`. -/
def real_input_40_arity_charge_det_closed_P7 (Λ q : ℚ) : ℚ :=
  q * (1 - q) + q * (4 * q - 3) * Λ + (-4 * q ^ 2 - q + 1) * Λ ^ 2 +
    (6 * q ^ 2 - 3 * q - 1) * Λ ^ 3 + 6 * q * Λ ^ 4 + (1 - 5 * q) * Λ ^ 5 -
    2 * Λ ^ 6 + Λ ^ 7

/-- The generated determinant factorization in the `z`-chart. -/
def real_input_40_arity_charge_det_closed_det (z q : ℚ) : ℚ :=
  (1 + z) * (1 - q * z ^ 2) * real_input_40_arity_charge_det_closed_Q7 z q

/-- The generated determinant factorization in the reciprocal `Λ`-chart. -/
def real_input_40_arity_charge_det_closed_charpoly (Λ q : ℚ) : ℚ :=
  Λ ^ 10 * (Λ + 1) * (Λ ^ 2 - q) * real_input_40_arity_charge_det_closed_P7 Λ q

lemma real_input_40_arity_charge_det_closed_P7_reciprocal
    (Λ q : ℚ) (hΛ : Λ ≠ 0) :
    real_input_40_arity_charge_det_closed_P7 Λ q =
      Λ ^ 7 * real_input_40_arity_charge_det_closed_Q7 Λ⁻¹ q := by
  unfold real_input_40_arity_charge_det_closed_P7 real_input_40_arity_charge_det_closed_Q7
  field_simp [hΛ]
  ring

/-- Paper label: `thm:real-input-40-arity-charge-det-closed`. The generated arity-charge audit
packages the explicit determinant factorization in the `z`-chart, the reciprocal degree-`7`
polynomial in the Perron variable `Λ`, and the exact `P₇(Λ,q) = Λ⁷ Q₇(Λ⁻¹,q)` conversion. -/
theorem paper_real_input_40_arity_charge_det_closed :
    (∀ z q : ℚ,
      real_input_40_arity_charge_det_closed_det z q =
        (1 + z) * (1 - q * z ^ 2) * real_input_40_arity_charge_det_closed_Q7 z q) ∧
      (∀ Λ q : ℚ,
        real_input_40_arity_charge_det_closed_charpoly Λ q =
          Λ ^ 10 * (Λ + 1) * (Λ ^ 2 - q) * real_input_40_arity_charge_det_closed_P7 Λ q) ∧
      (∀ Λ q : ℚ, Λ ≠ 0 →
        real_input_40_arity_charge_det_closed_P7 Λ q =
          Λ ^ 7 * real_input_40_arity_charge_det_closed_Q7 Λ⁻¹ q) ∧
      (∀ q : ℚ,
        real_input_40_arity_charge_det_closed_det (-1) q = 0 ∧
          real_input_40_arity_charge_det_closed_charpoly 0 q = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z q
    rfl
  · intro Λ q
    rfl
  · intro Λ q hΛ
    exact real_input_40_arity_charge_det_closed_P7_reciprocal Λ q hΛ
  · intro q
    constructor <;> simp [real_input_40_arity_charge_det_closed_det,
      real_input_40_arity_charge_det_closed_charpoly]

end Omega.SyncKernelWeighted
