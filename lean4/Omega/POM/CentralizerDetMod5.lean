import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Omega.Graph.TransferMatrix

namespace Omega.POM.CentralizerDetMod5

open Matrix

/-- Centralizer determinant formula: det(aI + bA) = a² + ab - b².
    prop:pom-centralizer-det-norm-mod5 -/
theorem centralizer_det_formula (a b : ℤ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) ℤ) + b • Graph.goldenMeanAdjacency).det =
      a ^ 2 + a * b - b ^ 2 := by
  simp only [det_fin_two]
  simp only [Graph.goldenMeanAdjacency, smul_apply, one_apply, add_apply,
    Fin.isValue]
  norm_num
  ring

/-- The centralizer determinant mod 5 is a perfect square mod 5.
    prop:pom-centralizer-det-norm-mod5 -/
theorem det_mod5_is_square (a b : ℤ) :
    (a ^ 2 + a * b - b ^ 2) % 5 = ((a + 3 * b) ^ 2) % 5 := by
  have : (a + 3 * b) ^ 2 - (a ^ 2 + a * b - b ^ 2) = 5 * (a * b + 2 * b ^ 2) := by ring
  omega

/-- The golden-ratio minimal polynomial has discriminant 5.
    prop:pom-centralizer-det-norm-mod5 -/
theorem golden_ratio_discriminant : 1 ^ 2 + 4 * 1 = 5 := by norm_num

/-- The golden-ratio polynomial x² - x - 1 factors as (x - 3)² over Z/5.
    prop:pom-centralizer-det-norm-mod5 -/
theorem golden_poly_mod5_double_root :
    ∀ τ : ZMod 5, τ ^ 2 - τ - 1 = (τ - 3) ^ 2 := by decide

/-- Paper seeds: centralizer determinant at small values.
    prop:pom-centralizer-det-norm-mod5 -/
theorem paper_pom_centralizer_det_mod5 :
    (1 ^ 2 + 1 * 0 - 0 ^ 2 = (1 : ℤ)) ∧
    (0 ^ 2 + 0 * 1 - 1 ^ 2 = (-1 : ℤ)) ∧
    (1 ^ 2 + 1 * 1 - 1 ^ 2 = (1 : ℤ)) ∧
    (2 ^ 2 + 2 * 1 - 1 ^ 2 = (5 : ℤ)) ∧
    (1 ^ 2 + 4 * 1 = 5) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Omega.POM.CentralizerDetMod5
