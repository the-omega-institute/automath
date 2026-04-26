import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-cm-rigidity-qsqrtm15`. The quadratic relation forces the
completed-square discriminant `-15` and, after dividing by the nonzero root, the reciprocal
sum identity. -/
theorem paper_pom_cm_rigidity_qsqrtm15 (z : ℂ) (hz : 2 * z ^ 2 + z + 2 = 0) :
    (4 * z + 1) ^ 2 = -(15 : ℂ) ∧ z + z⁻¹ = -(1 / 2 : ℂ) := by
  have hz_ne : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    norm_num at hz
  constructor
  · have hsq : (4 * z + 1) ^ 2 + (15 : ℂ) = 0 := by
      calc
        (4 * z + 1) ^ 2 + (15 : ℂ) = 8 * (2 * z ^ 2 + z + 2) := by ring
        _ = 0 := by rw [hz]; ring
    exact eq_neg_of_add_eq_zero_left hsq
  · have hdiv : 2 * z + 1 + 2 * z⁻¹ = 0 := by
      have hmul := congrArg (fun w : ℂ => w * z⁻¹) hz
      simpa [pow_two, mul_add, add_mul, mul_assoc, hz_ne] using hmul
    linear_combination (1 / 2 : ℂ) * hdiv

end Omega.POM
