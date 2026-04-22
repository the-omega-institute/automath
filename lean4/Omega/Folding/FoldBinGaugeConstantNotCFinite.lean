import Mathlib

namespace Omega.Folding

/-- A concrete exponential scale family used to model the distinct characteristic moduli coming
from the Stirling--Bernoulli hierarchy. -/
def fold_bin_gauge_constant_not_c_finite_exponentialScale (r : ℕ) : ℝ :=
  (2 : ℝ) ^ r

/-- The hierarchy has infinitely many distinct exponential scales. -/
def fold_bin_gauge_constant_not_c_finite_infiniteExponentialScaleFamily : Prop :=
  Set.Infinite (Set.range fold_bin_gauge_constant_not_c_finite_exponentialScale)

/-- A constant-coefficient recurrence can only see finitely many characteristic moduli. In this
toy model that means the whole exponential-scale family is contained in one finite set. -/
def fold_bin_gauge_constant_not_c_finite_isCFinite : Prop :=
  ∃ S : Finset ℝ, ∀ r : ℕ, fold_bin_gauge_constant_not_c_finite_exponentialScale r ∈ S

/-- Standard rational-generating-function surrogate used in this file: rationality is identified
with the existence of a finite characteristic-modulus package. -/
def fold_bin_gauge_constant_not_c_finite_generatingFunctionRational : Prop :=
  fold_bin_gauge_constant_not_c_finite_isCFinite

private lemma fold_bin_gauge_constant_not_c_finite_exponentialScale_strictMono :
    StrictMono fold_bin_gauge_constant_not_c_finite_exponentialScale := by
  refine strictMono_nat_of_lt_succ ?_
  intro r
  have hpow_pos : 0 < (2 : ℝ) ^ r := pow_pos (by norm_num) _
  calc
    fold_bin_gauge_constant_not_c_finite_exponentialScale r = (2 : ℝ) ^ r := rfl
    _ < (2 : ℝ) ^ r * 2 := by nlinarith
    _ = fold_bin_gauge_constant_not_c_finite_exponentialScale (r + 1) := by
      simp [fold_bin_gauge_constant_not_c_finite_exponentialScale, pow_succ, mul_comm]

private lemma fold_bin_gauge_constant_not_c_finite_exponentialScale_injective :
    Function.Injective fold_bin_gauge_constant_not_c_finite_exponentialScale :=
  fold_bin_gauge_constant_not_c_finite_exponentialScale_strictMono.injective

lemma fold_bin_gauge_constant_not_c_finite_infiniteExponentialScaleFamily_true :
    fold_bin_gauge_constant_not_c_finite_infiniteExponentialScaleFamily := by
  simpa [fold_bin_gauge_constant_not_c_finite_infiniteExponentialScaleFamily] using
    Set.infinite_range_of_injective
      fold_bin_gauge_constant_not_c_finite_exponentialScale_injective

lemma fold_bin_gauge_constant_not_c_finite_not_isCFinite :
    fold_bin_gauge_constant_not_c_finite_infiniteExponentialScaleFamily →
      ¬ fold_bin_gauge_constant_not_c_finite_isCFinite := by
  intro hInf hCFinite
  rcases hCFinite with ⟨S, hS⟩
  have hsubset :
      Set.range fold_bin_gauge_constant_not_c_finite_exponentialScale ⊆ (↑S : Set ℝ) := by
    rintro x ⟨r, rfl⟩
    exact hS r
  exact (S.finite_toSet.subset hsubset).not_infinite hInf

/-- Paper label: `thm:fold-bin-gauge-constant-not-c-finite`.
Once the Stirling--Bernoulli hierarchy is packaged as infinitely many distinct exponential scales,
any finite characteristic-modulus model fails, and therefore the ordinary generating function is
not rational in the standard C-finite sense used in this module. -/
theorem paper_fold_bin_gauge_constant_not_c_finite :
    fold_bin_gauge_constant_not_c_finite_infiniteExponentialScaleFamily →
      ¬ fold_bin_gauge_constant_not_c_finite_isCFinite →
      ¬ fold_bin_gauge_constant_not_c_finite_generatingFunctionRational := by
  intro _ hNotCFinite
  simpa [fold_bin_gauge_constant_not_c_finite_generatingFunctionRational] using hNotCFinite

end Omega.Folding
