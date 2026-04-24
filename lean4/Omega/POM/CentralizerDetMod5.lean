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

/-- The mod-`5` reduction is the unique prime where the golden-ratio polynomial acquires a
double root.  Paper label: `cor:pom-centralizer-unique-bad-prime-5`. -/
theorem paper_pom_centralizer_unique_bad_prime_5 :
    (∀ τ : ZMod 5, τ ^ 2 - τ - 1 = (τ - 3) ^ 2) ∧
      ¬∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ ∀ τ : ZMod p, τ ^ 2 - τ - 1 = (τ - 3) ^ 2 := by
  refine ⟨golden_poly_mod5_double_root, ?_⟩
  rintro ⟨p, hp, hp_ne, hsquare⟩
  have hfive_zmod : (5 : ZMod p) = 0 := by
    have h1 := hsquare (1 : ZMod p)
    norm_num at h1
    have h2 := congrArg (fun z : ZMod p => z + 1) h1
    norm_num at h2
    simpa using h2.symm
  have hpdvd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp hfive_zmod
  have hp_eq : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hpdvd
  exact hp_ne hp_eq

end Omega.POM.CentralizerDetMod5
