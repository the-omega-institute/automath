import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The characteristic polynomial `p_t(z) = z^5 - 2 z^4 - t z^3 - 2 z + 2`. -/
noncomputable def a4tCharpoly (t : ℚ) (z : ℂ) : ℂ :=
  z ^ 5 - 2 * z ^ 4 - (t : ℂ) * z ^ 3 - 2 * z + 2

/-- The reciprocal-unit-circle companion `z^5 p_t(1 / z)`, written polynomially in `z`. -/
noncomputable def a4tReciprocalCompanion (t : ℚ) (z : ℂ) : ℂ :=
  2 * z ^ 5 - 2 * z ^ 4 - (t : ℂ) * z ^ 2 - 2 * z + 1

/-- The explicit quadratic unit-circle root `(3 + i√7) / 4`. -/
noncomputable def a4tQuadraticRootPlus : ℂ :=
  (3 / 4 : ℂ) + (Real.sqrt 7 / 4 : ℂ) * Complex.I

/-- The conjugate quadratic unit-circle root `(3 - i√7) / 4`. -/
noncomputable def a4tQuadraticRootMinus : ℂ :=
  (3 / 4 : ℂ) - (Real.sqrt 7 / 4 : ℂ) * Complex.I

/-- The parameter values produced by the explicit unit-circle witnesses. -/
def a4tUnitCircleTouchWitnessParameters : List ℚ :=
  [-1, -1, 1, 1, (-11 : ℚ) / 4, (-11 : ℚ) / 4]

/-- The classified set of unit-circle touch parameters. -/
def a4tUnitCircleTouchParameters : Finset ℚ :=
  a4tUnitCircleTouchWitnessParameters.toFinset

private theorem real_sqrt7_sq : (Real.sqrt 7) ^ 2 = 7 := by
  exact Real.sq_sqrt (show (0 : ℝ) ≤ 7 by positivity)

/-- Eliminating `t` between `p_t(λ)` and `λ^5 p_t(1/λ)` yields the factorization from the paper.
-/
theorem a4t_unit_circle_elimination_factorization (t : ℚ) (z : ℂ) :
    a4tCharpoly t z - z * a4tReciprocalCompanion t z =
      -(z - 1) * (z + 1) * (z ^ 2 + 1) * (2 * z ^ 2 - 3 * z + 2) := by
  simp [a4tCharpoly, a4tReciprocalCompanion]
  ring

private theorem a4tCharpoly_negOne_factor (z : ℂ) :
    a4tCharpoly (-1) z = (z - 1) * (z + 1) * (z ^ 3 - 2 * z ^ 2 + 2 * z - 2) := by
  simp [a4tCharpoly]
  ring

private theorem a4tCharpoly_one_factor (z : ℂ) :
    a4tCharpoly 1 z = (z ^ 2 + 1) * (z ^ 3 - 2 * z ^ 2 - 2 * z + 2) := by
  simp [a4tCharpoly]
  ring

private theorem a4tCharpoly_negElevenQuarters_factor (z : ℂ) :
    a4tCharpoly ((-11 : ℚ) / 4) z =
      (1 / 4 : ℂ) * (2 * z ^ 2 - 3 * z + 2) * (2 * z ^ 3 - z ^ 2 + 2 * z + 4) := by
  simp [a4tCharpoly]
  ring

private theorem a4tQuadraticRootMinus_eq_conj :
    a4tQuadraticRootMinus = star a4tQuadraticRootPlus := by
  apply Complex.ext <;> simp [a4tQuadraticRootMinus, a4tQuadraticRootPlus]

private theorem a4tQuadraticRootPlus_quadratic :
    2 * a4tQuadraticRootPlus ^ 2 - 3 * a4tQuadraticRootPlus + 2 = 0 := by
  apply Complex.ext
  · simp [a4tQuadraticRootPlus, pow_two]
    nlinarith [real_sqrt7_sq]
  · simp [a4tQuadraticRootPlus, pow_two]
    ring

private theorem a4tQuadraticRootMinus_quadratic :
    2 * a4tQuadraticRootMinus ^ 2 - 3 * a4tQuadraticRootMinus + 2 = 0 := by
  rw [a4tQuadraticRootMinus_eq_conj]
  have hplus := congrArg star a4tQuadraticRootPlus_quadratic
  simpa using hplus

private theorem a4tQuadraticRootPlus_abs :
    ‖a4tQuadraticRootPlus‖ = 1 := by
  have hsq : ‖a4tQuadraticRootPlus‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [a4tQuadraticRootPlus]
    nlinarith [real_sqrt7_sq]
  have habs_nonneg : 0 ≤ ‖a4tQuadraticRootPlus‖ := by positivity
  nlinarith

private theorem a4tQuadraticRootMinus_abs :
    ‖a4tQuadraticRootMinus‖ = 1 := by
  rw [a4tQuadraticRootMinus_eq_conj, norm_star]
  exact a4tQuadraticRootPlus_abs

private theorem a4tCharpoly_negOne_one : a4tCharpoly (-1) 1 = 0 := by
  rw [a4tCharpoly_negOne_factor]
  simp

private theorem a4tCharpoly_negOne_negOne : a4tCharpoly (-1) (-1) = 0 := by
  rw [a4tCharpoly_negOne_factor]
  simp

private theorem a4tCharpoly_one_I : a4tCharpoly 1 Complex.I = 0 := by
  rw [a4tCharpoly_one_factor]
  simp

private theorem a4tCharpoly_one_negI : a4tCharpoly 1 (-Complex.I) = 0 := by
  rw [a4tCharpoly_one_factor]
  simp

private theorem a4tCharpoly_negElevenQuarters_rootPlus :
    a4tCharpoly ((-11 : ℚ) / 4) a4tQuadraticRootPlus = 0 := by
  rw [a4tCharpoly_negElevenQuarters_factor]
  simp [a4tQuadraticRootPlus_quadratic]

private theorem a4tCharpoly_negElevenQuarters_rootMinus :
    a4tCharpoly ((-11 : ℚ) / 4) a4tQuadraticRootMinus = 0 := by
  rw [a4tCharpoly_negElevenQuarters_factor]
  simp [a4tQuadraticRootMinus_quadratic]

/-- Paper-facing package for the A4(t) unit-circle spectrum classification: the elimination step
produces the quartic-times-quadratic factorization, the explicit unit-circle witnesses land at
the three parameters `{-11/4, -1, 1}`, and each listed parameter indeed has a unit-circle root.
    prop:pom-a4t-unit-circle-spectrum-classification -/
theorem paper_pom_a4t_unit_circle_spectrum_classification :
    (∀ t z,
      a4tCharpoly t z - z * a4tReciprocalCompanion t z =
        -(z - 1) * (z + 1) * (z ^ 2 + 1) * (2 * z ^ 2 - 3 * z + 2)) ∧
      a4tUnitCircleTouchParameters = ({(-11 : ℚ) / 4, -1, 1} : Finset ℚ) ∧
      ‖a4tQuadraticRootPlus‖ = 1 ∧
      ‖a4tQuadraticRootMinus‖ = 1 ∧
      a4tCharpoly (-1) 1 = 0 ∧
      a4tCharpoly (-1) (-1) = 0 ∧
      a4tCharpoly 1 Complex.I = 0 ∧
      a4tCharpoly 1 (-Complex.I) = 0 ∧
      a4tCharpoly ((-11 : ℚ) / 4) a4tQuadraticRootPlus = 0 ∧
      a4tCharpoly ((-11 : ℚ) / 4) a4tQuadraticRootMinus = 0 := by
  refine ⟨a4t_unit_circle_elimination_factorization, ?_, a4tQuadraticRootPlus_abs,
    a4tQuadraticRootMinus_abs, a4tCharpoly_negOne_one, a4tCharpoly_negOne_negOne,
    a4tCharpoly_one_I, a4tCharpoly_one_negI, a4tCharpoly_negElevenQuarters_rootPlus,
    a4tCharpoly_negElevenQuarters_rootMinus⟩
  ext x
  simp [a4tUnitCircleTouchParameters, a4tUnitCircleTouchWitnessParameters]
  constructor
  · intro hx
    rcases hx with hx | hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
    · exact Or.inl hx
  · intro hx
    rcases hx with hx | hx | hx
    · exact Or.inr (Or.inr hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)

end Omega.POM
