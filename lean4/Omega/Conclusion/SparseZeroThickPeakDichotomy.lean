import Mathlib.Tactic
import Omega.Conclusion.ZeroSparsityNonuniformityLocalbiasFaithfulness

namespace Omega.Conclusion

/-- Concrete sparse-zero/thick-peak package.  The scale `fibScale m` is the Fibonacci-sized
ambient space, `zeroCount m` is the zero block count, and `peakRatio m` is the normalized
max-fiber bias. -/
structure conclusion_sparse_zero_thick_peak_dichotomy_data where
  zeroCount : ℕ → ℝ
  fibScale : ℕ → ℝ
  divisorWeight : ℕ → ℝ
  halfFibScale : ℕ → ℝ
  peakRatio : ℕ → ℝ
  thickConstant : ℝ
  sparse_zero_density_upper :
    ∀ m : ℕ, zeroCount m / fibScale m ≤ divisorWeight m * halfFibScale m / fibScale m
  thick_peak_lower_bound :
    ∀ m : ℕ, 1 + thickConstant ≤ peakRatio m

/-- The sparse zero-density upper bound and thick-peak lower bound hold simultaneously. -/
def conclusion_sparse_zero_thick_peak_dichotomy_statement
    (D : conclusion_sparse_zero_thick_peak_dichotomy_data) : Prop :=
  (∀ m : ℕ, D.zeroCount m / D.fibScale m ≤
      D.divisorWeight m * D.halfFibScale m / D.fibScale m) ∧
    (∀ m : ℕ, 1 + D.thickConstant ≤ D.peakRatio m) ∧
    ∀ m : ℕ,
      D.zeroCount m / D.fibScale m ≤
          D.divisorWeight m * D.halfFibScale m / D.fibScale m ∧
        1 + D.thickConstant ≤ D.peakRatio m

/-- Paper label: `thm:conclusion-sparse-zero-thick-peak-dichotomy`. -/
theorem paper_conclusion_sparse_zero_thick_peak_dichotomy
    (D : conclusion_sparse_zero_thick_peak_dichotomy_data) :
    conclusion_sparse_zero_thick_peak_dichotomy_statement D := by
  exact ⟨D.sparse_zero_density_upper, D.thick_peak_lower_bound,
    fun m => ⟨D.sparse_zero_density_upper m, D.thick_peak_lower_bound m⟩⟩

end Omega.Conclusion
