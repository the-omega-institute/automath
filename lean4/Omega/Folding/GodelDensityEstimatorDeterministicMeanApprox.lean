import Mathlib

open scoped BigOperators

namespace Omega.Folding

/-- The `0/1` indicator attached to a Boolean bit. -/
def boolBit (b : Bool) : ℝ :=
  if b then 1 else 0

/-- The prime-log normalizing factor `Θ_n = ∑_{j ≤ n} log p_j` for the first `n` primes. -/
noncomputable def godelTheta (n : ℕ) : ℝ :=
  ∑ j : Fin n, Real.log ((Nat.nth Nat.Prime j.1 : ℕ) : ℝ)

/-- The normalized prime-log weight `w_{n,j} = log p_j / Θ_n`. -/
noncomputable def godelPrimeLogWeight (n : ℕ) (j : Fin n) : ℝ :=
  Real.log ((Nat.nth Nat.Prime j.1 : ℕ) : ℝ) / godelTheta n

/-- The Gödel density estimator `\hat d_n(x)`. -/
noncomputable def godelDensityEstimator (n : ℕ) (x : Fin n → Bool) : ℝ :=
  ∑ j : Fin n, godelPrimeLogWeight n j * boolBit (x j)

/-- The ordinary empirical mean `\bar x_n`. -/
noncomputable def empiricalMean (n : ℕ) (x : Fin n → Bool) : ℝ :=
  (∑ j : Fin n, boolBit (x j)) / (n : ℝ)

/-- The deterministic approximation reduces the estimator-minus-mean error to the `L¹` deviation
between the prime-log weights and the uniform weights.
    thm:fold-godel-density-estimator-deterministic-mean-approx -/
theorem paper_fold_godel_density_estimator_deterministic_mean_approx (n : ℕ) :
    ∀ x : Fin n → Bool,
      |godelDensityEstimator n x - empiricalMean n x| ≤
        ∑ j : Fin n, |godelPrimeLogWeight n j - 1 / (n : ℝ)| := by
  intro x
  have hrewrite :
      godelDensityEstimator n x - empiricalMean n x =
        ∑ j : Fin n, (godelPrimeLogWeight n j - 1 / (n : ℝ)) * boolBit (x j) := by
    unfold godelDensityEstimator empiricalMean
    calc
      (∑ j : Fin n, godelPrimeLogWeight n j * boolBit (x j)) -
          (∑ j : Fin n, boolBit (x j)) / (n : ℝ)
          =
        (∑ j : Fin n, godelPrimeLogWeight n j * boolBit (x j)) -
          ∑ j : Fin n, boolBit (x j) * ((n : ℝ)⁻¹) := by
            rw [div_eq_mul_inv, Finset.sum_mul]
      _ = ∑ j : Fin n,
            (godelPrimeLogWeight n j * boolBit (x j) - boolBit (x j) * ((n : ℝ)⁻¹)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ j : Fin n, (godelPrimeLogWeight n j - 1 / (n : ℝ)) * boolBit (x j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
  rw [hrewrite]
  calc
    |∑ j : Fin n, (godelPrimeLogWeight n j - 1 / (n : ℝ)) * boolBit (x j)| ≤
        ∑ j : Fin n, |godelPrimeLogWeight n j - 1 / (n : ℝ)| * |boolBit (x j)| := by
          simpa [abs_mul] using
            (Finset.abs_sum_le_sum_abs
              (s := Finset.univ)
              (f := fun j : Fin n => (godelPrimeLogWeight n j - 1 / (n : ℝ)) * boolBit (x j)))
    _ = ∑ j : Fin n, |godelPrimeLogWeight n j - 1 / (n : ℝ)| * boolBit (x j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hx : x j <;> simp [boolBit, hx]
    _ ≤ ∑ j : Fin n, |godelPrimeLogWeight n j - 1 / (n : ℝ)| := by
          refine Finset.sum_le_sum ?_
          intro j hj
          by_cases hx : x j <;> simp [boolBit, hx]
