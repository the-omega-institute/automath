import Mathlib.Data.Fintype.BigOperators
import Omega.POM.MicrocanonicalFoldBayesSuccessNminusT
import Omega.POM.MicrocanonicalFoldHtFromPowerSums

namespace Omega.POM

open scoped BigOperators

/-- Paper label: `thm:pom-microcanonical-fold-bayes-success-polynomial-in-moments`.
For fold data `d = d_m` of total mass `N = 2^m`, the exact `N - t` Bayes-success package is read
through the normalized weights `w_m(x) = d_m(x) / 2^m`. Writing the collision moments as
`S_k(m) = ∑ x, d_m(x)^k`, the fold power sums satisfy `p_k(w_m) = 2^{-mk} S_k(m)`, so the low
complete-homogeneous coefficients governing the thermodynamic Bayes-success regime are explicit
polynomials in the low moments. -/
def paper_pom_microcanonical_fold_bayes_success_polynomial_in_moments : Prop := by
  exact
    ∀ {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℕ) (m t : ℕ),
      microcanonicalTotalMass d = 2 ^ m →
        let w : α → ℝ := fun x => (d x : ℝ) / ((2 : ℝ) ^ m);
        let S : ℕ → ℝ := fun k => ∑ x : α, (d x : ℝ) ^ k;
        let p : ℕ → ℝ := fun k => pom_microcanonical_fold_ht_from_power_sums_powerSum w k;
        (∀ r : α → ℕ,
            microcanonicalResidualCompletionCount r =
              Nat.factorial (microcanonicalTotalMass r) / ∏ x : α, Nat.factorial (r x)) ∧
          (∀ r : α → ℕ,
            microcanonicalResidualBayesSuccess r =
              (∏ x : α, (Nat.factorial (r x) : ℚ)) /
                (Nat.factorial (microcanonicalTotalMass r) : ℚ)) ∧
          (microcanonicalBayesSuccessNminusT d t =
            Finset.sum (microcanonicalResidualCountProfiles (α := α) t) fun r =>
              if ∑ x : α, (r x : ℕ) = t then
                ((∏ x : α, (Nat.factorial ((r x : Fin (t + 1)) : ℕ) : ℚ)) /
                  (Nat.factorial t : ℚ)) *
                  ((∏ x : α, (Nat.descFactorial (d x) ((r x : Fin (t + 1)) : ℕ) : ℚ)) /
                    (Nat.descFactorial (microcanonicalTotalMass d) t : ℚ))
              else 0) ∧
          (∀ k : ℕ, p k = S k / ((2 : ℝ) ^ (m * k))) ∧
          p 2 = S 2 / ((2 : ℝ) ^ (2 * m)) ∧
          p 3 = S 3 / ((2 : ℝ) ^ (3 * m)) ∧
          pom_microcanonical_fold_ht_from_power_sums_h2 w =
            (1 + S 2 / ((2 : ℝ) ^ (2 * m))) / 2 ∧
          pom_microcanonical_fold_ht_from_power_sums_h3 w =
            (1 + 3 * S 2 / ((2 : ℝ) ^ (2 * m)) + 2 * S 3 / ((2 : ℝ) ^ (3 * m))) / 6 ∧
          pom_microcanonical_fold_ht_from_power_sums_h4 w =
            (1 + 6 * S 2 / ((2 : ℝ) ^ (2 * m)) +
              3 * (S 2 / ((2 : ℝ) ^ (2 * m))) ^ 2 + 8 * S 3 / ((2 : ℝ) ^ (3 * m)) +
              6 * S 4 / ((2 : ℝ) ^ (4 * m))) / 24 ∧
          pom_microcanonical_fold_ht_from_power_sums_h5 w =
            (1 + 10 * S 2 / ((2 : ℝ) ^ (2 * m)) +
              15 * (S 2 / ((2 : ℝ) ^ (2 * m))) ^ 2 + 20 * S 3 / ((2 : ℝ) ^ (3 * m)) +
              20 * (S 2 / ((2 : ℝ) ^ (2 * m))) * (S 3 / ((2 : ℝ) ^ (3 * m))) +
              30 * S 4 / ((2 : ℝ) ^ (4 * m)) + 24 * S 5 / ((2 : ℝ) ^ (5 * m))) / 120

end Omega.POM
