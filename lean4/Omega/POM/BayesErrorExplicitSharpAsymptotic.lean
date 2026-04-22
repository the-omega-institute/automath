import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Bayes error tail rewritten as a pure golden-ratio power sum.
    thm:pom-bayes-error-explicit-sharp-asymptotic -/
theorem paper_pom_bayes_error_explicit_sharp_asymptotic (n : Nat) :
    let phi : Real := Real.goldenRatio
    let p : Real := phi⁻¹
    let q : Real := phi ^ (-2 : Int)
    Finset.sum (Finset.range (n / 2 + 1)) (fun j => (Nat.choose n j : Real) * p ^ j * q ^ (n - j)) =
      Finset.sum (Finset.range (n / 2 + 1))
        (fun j => (Nat.choose n j : Real) * phi ^ ((j : Int) - 2 * (n : Int))) := by
  dsimp
  set φ : Real := Real.goldenRatio
  have hφ_pos : 0 < φ := by simpa [φ] using Real.goldenRatio_pos
  have hφ_ne : φ ≠ 0 := ne_of_gt hφ_pos
  have hq_ne : (φ ^ (-2 : Int) : Real) ≠ 0 := zpow_ne_zero _ hφ_ne
  have hratio : (φ⁻¹ : Real) / (φ ^ (-2 : Int)) = φ := by
    field_simp [hφ_ne]
  have hqpow : (φ ^ (-2 : Int) : Real) ^ n = φ ^ ((-2 : Int) * (n : Int)) := by
    simpa [zpow_natCast] using (zpow_mul φ (-2) (n : Int)).symm
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj_lt : j < n / 2 + 1 := Finset.mem_range.1 hj
  have hj_le_half : j ≤ n / 2 := Nat.lt_succ_iff.1 hj_lt
  have hj_le_n : j ≤ n := le_trans hj_le_half (Nat.div_le_self n 2)
  have hsplit :
      (φ⁻¹ : Real) ^ j * (φ ^ (-2 : Int)) ^ (n - j) =
        (((φ⁻¹ : Real) / (φ ^ (-2 : Int))) ^ j) * (φ ^ (-2 : Int)) ^ n := by
    calc
      (φ⁻¹ : Real) ^ j * (φ ^ (-2 : Int)) ^ (n - j) =
          (((φ⁻¹ : Real) ^ j) / ((φ ^ (-2 : Int)) ^ j)) *
            (((φ ^ (-2 : Int)) ^ j) * (φ ^ (-2 : Int)) ^ (n - j)) := by
              field_simp [pow_ne_zero _ hq_ne]
      _ = (((φ⁻¹ : Real) / (φ ^ (-2 : Int))) ^ j) * (φ ^ (-2 : Int)) ^ n := by
            rw [div_pow, ← pow_add, Nat.add_sub_of_le hj_le_n]
  calc
    (Nat.choose n j : Real) * (φ⁻¹ : Real) ^ j * (φ ^ (-2 : Int)) ^ (n - j) =
        (Nat.choose n j : Real) *
          ((((φ⁻¹ : Real) / (φ ^ (-2 : Int))) ^ j) * (φ ^ (-2 : Int)) ^ n) := by
          rw [mul_assoc, hsplit]
    _ = (Nat.choose n j : Real) * (φ ^ ((j : Nat) : Int) * φ ^ ((-2 : Int) * (n : Int))) := by
          rw [hratio, hqpow, zpow_natCast]
    _ = (Nat.choose n j : Real) * φ ^ (((j : Nat) : Int) + ((-2 : Int) * (n : Int))) := by
          congr 1
          rw [← zpow_add₀ hφ_ne]
    _ = (Nat.choose n j : Real) * φ ^ ((j : Int) - 2 * (n : Int)) := by
          congr 1

end Omega.POM
