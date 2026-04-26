import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Folding.FoldPadicSaturationFiniteSet
import Omega.Folding.TypicalFiberPolynomialSmoothness

namespace Omega.Folding

/-- The smoothness event contributes zero failure weight once the typical-fiber bound is known. -/
noncomputable def fold_saturation_smooth_dichotomy_failure_weight (m ell : ℕ) : ℝ := by
  classical
  exact if typicalFiberLogSmoothHighProbability m ell then 0 else 1

/-- Union-bound failure budget combining the smoothness event with the finite-set `p`-adic
saturation event. -/
noncomputable def fold_saturation_smooth_dichotomy_joint_failure_bound
    (S : Finset ℕ) (z : ℕ) (a : ZMod z) (m ell : ℕ) (μ : ℝ) : ℝ :=
  fold_saturation_smooth_dichotomy_failure_weight m ell +
    (S.card : ℝ) * componentResidueLowerTailProb z a m μ

/-- Concrete corollary combining the typical-fiber smoothness event with the finite-set `p`-adic
saturation package through a union-bound estimate.
    cor:fold-saturation-smooth-dichotomy -/
def fold_saturation_smooth_dichotomy_statement : Prop :=
  ∀ (S : Finset ℕ) (z m ell : ℕ) (a : ZMod z),
    2 ≤ z →
    2 * z ≤ m →
    ell ≤ Nat.log 2 (m + 1) →
    (∀ p ∈ S, Nat.Prime p) →
    (∀ p ∈ S, foldPrimeEntryPointDivisibility p z) →
      ∃ μ c : ℝ,
        0 < μ ∧
          0 < c ∧
          typicalFiberLogSmoothHighProbability m ell ∧
          typicalFiberPolynomialPrimeFactorBound m ell ∧
          (∀ p ∈ S, foldPrimeEntryPointDivisibility p z ∧ foldLinearPadicSaturation z a) ∧
          fold_saturation_smooth_dichotomy_joint_failure_bound S z a m ell μ ≤
            ((S.card : ℝ) + 1) * Real.exp (-c * m)

theorem paper_fold_saturation_smooth_dichotomy : fold_saturation_smooth_dichotomy_statement := by
  intro S z m ell a hz hm hell hprime hentry
  have hsmooth := paper_fold_typical_fiber_polynomial_smoothness m ell hell
  rcases paper_fold_padic_saturation_finite_set S z a hz hprime hentry with
    ⟨μ, c, hμ, hc, hpadic, htail⟩
  refine ⟨μ, c, hμ, hc, hsmooth.1, hsmooth.2, hpadic, ?_⟩
  have hexp_nonneg : 0 ≤ Real.exp (-c * m) := by positivity
  have hweight :
      fold_saturation_smooth_dichotomy_failure_weight m ell = 0 := by
    classical
    simp [fold_saturation_smooth_dichotomy_failure_weight, hsmooth.1]
  calc
    fold_saturation_smooth_dichotomy_joint_failure_bound S z a m ell μ
        = 0 + (S.card : ℝ) * componentResidueLowerTailProb z a m μ := by
            simp [fold_saturation_smooth_dichotomy_joint_failure_bound, hweight]
    _ ≤ 0 + (S.card : ℝ) * Real.exp (-c * m) := by
          simpa using htail m hm
    _ ≤ ((S.card : ℝ) + 1) * Real.exp (-c * m) := by
          nlinarith

end Omega.Folding
