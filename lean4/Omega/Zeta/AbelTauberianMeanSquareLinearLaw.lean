import Mathlib

namespace Omega.Zeta

open Filter
open scoped BigOperators

noncomputable section

/-- Partial sums of the nonnegative sequence extracted from the Abel mean-square energy package. -/
def abel_tauberian_mean_square_linear_law_partial_sum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) a

/-- Chapter-local wrapper for the Tauberian hypothesis behind the Abel mean-square linear law. -/
structure abel_tauberian_mean_square_linear_law_data where
  seq : ℕ → ℝ
  slope : ℝ
  h_nonneg : ∀ n : ℕ, 0 ≤ seq n
  h_tauberian :
    Tendsto
      (fun N : ℕ => abel_tauberian_mean_square_linear_law_partial_sum seq N / (N + 1 : ℝ))
      atTop (nhds slope)

namespace abel_tauberian_mean_square_linear_law_data

/-- Linear asymptotic law for the partial sums of the Abel mean-square sequence. -/
def partial_sum_linear_law (D : abel_tauberian_mean_square_linear_law_data) : Prop :=
  Tendsto
    (fun N : ℕ => abel_tauberian_mean_square_linear_law_partial_sum D.seq N / (N + 1 : ℝ))
    atTop (nhds D.slope)

end abel_tauberian_mean_square_linear_law_data

/-- Paper label: `cor:abel-tauberian-mean-square-linear-law`. Once the nonnegative Abel
energy sequence is packaged with the Tauberian input from the preceding energy theorem, the
linear law for its partial sums is exactly that packaged conclusion. -/
theorem paper_abel_tauberian_mean_square_linear_law
    (D : abel_tauberian_mean_square_linear_law_data) : D.partial_sum_linear_law := by
  exact D.h_tauberian

end

end Omega.Zeta
