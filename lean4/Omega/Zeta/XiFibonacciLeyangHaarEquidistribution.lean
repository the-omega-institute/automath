import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

/-- Degree of the finite Fibonacci--Lee--Yang product
`∏_{j < m} (1 + z ^ F_{j+2})`. -/
def xi_fibonacci_leyang_haar_equidistribution_degree (m : ℕ) : ℕ :=
  (Finset.range m).sum fun j => Nat.fib (j + 2)

/-- Fourier-coefficient data for normalized zero-counting measures of the finite
Fibonacci--Lee--Yang products.  For each fixed nonzero mode, `modeSupportWeight` is the finite
total degree contributed by the finitely many Fibonacci divisors of that mode. -/
structure xi_fibonacci_leyang_haar_equidistribution_data where
  fourierCoeff : ℕ → ℤ → ℝ
  modeSupportWeight : ℤ → ℝ
  fourierCoeff_zero : ∀ m, fourierCoeff m 0 = 1
  fourierCoeff_abs_bound :
    ∀ m k, k ≠ 0 →
      |fourierCoeff m k| ≤
        modeSupportWeight k /
          (xi_fibonacci_leyang_haar_equidistribution_degree m : ℝ)
  degree_tendsto_atTop :
    Tendsto
      (fun m : ℕ => (xi_fibonacci_leyang_haar_equidistribution_degree m : ℝ))
      atTop atTop

namespace xi_fibonacci_leyang_haar_equidistribution_data

/-- Fourier formulation of convergence of the zero-counting measures to Haar measure. -/
def zeroMeasuresConvergeToHaar
    (D : xi_fibonacci_leyang_haar_equidistribution_data) : Prop :=
  (∀ m, D.fourierCoeff m 0 = 1) ∧
    ∀ k : ℤ, k ≠ 0 → Tendsto (fun m : ℕ => D.fourierCoeff m k) atTop (nhds 0)

end xi_fibonacci_leyang_haar_equidistribution_data

/-- Paper label: `thm:xi-fibonacci-leyang-haar-equidistribution`. -/
theorem paper_xi_fibonacci_leyang_haar_equidistribution
    (D : xi_fibonacci_leyang_haar_equidistribution_data) :
    D.zeroMeasuresConvergeToHaar := by
  refine ⟨D.fourierCoeff_zero, ?_⟩
  intro k hk
  have hupper :
      Tendsto
        (fun m : ℕ =>
          D.modeSupportWeight k /
            (xi_fibonacci_leyang_haar_equidistribution_degree m : ℝ))
        atTop (nhds 0) :=
    D.degree_tendsto_atTop.const_div_atTop (D.modeSupportWeight k)
  have habs :
      Tendsto (fun m : ℕ => |D.fourierCoeff m k|) atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun m => D.fourierCoeff_abs_bound m k hk) hupper
  exact (tendsto_zero_iff_abs_tendsto_zero
    (fun m : ℕ => D.fourierCoeff m k)).2 habs

end Omega.Zeta
