import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- The adjacency spectral-layer multiplicity for five disjoint `2n`-cubes. -/
def xi_time_part76_leyang_branch_hypercube_spectrum_heat_adjMultiplicity
    (n j : ℕ) : ℕ :=
  5 * Nat.choose (2 * n) j

/-- The heat trace obtained by summing the Laplacian eigenvalue layers of five disjoint cubes. -/
noncomputable def xi_time_part76_leyang_branch_hypercube_spectrum_heat_trace
    (n : ℕ) (t : ℝ) : ℝ :=
  5 * (∑ j ∈ range (2 * n + 1),
    (Nat.choose (2 * n) j : ℝ) * (Real.exp (-2 * t)) ^ j)

/-- Paper label: `thm:xi-time-part76-leyang-branch-hypercube-spectrum-heat`. -/
theorem paper_xi_time_part76_leyang_branch_hypercube_spectrum_heat (n : ℕ) :
    (∀ j : ℕ, j ≤ 2 * n →
      xi_time_part76_leyang_branch_hypercube_spectrum_heat_adjMultiplicity n j =
        5 * Nat.choose (2 * n) j) ∧
    (∀ t : ℝ, 0 ≤ t →
      xi_time_part76_leyang_branch_hypercube_spectrum_heat_trace n t =
        5 * (1 + Real.exp (-2 * t)) ^ (2 * n)) := by
  refine ⟨?_, ?_⟩
  · intro j _hj
    rfl
  · intro t _ht
    let x : ℝ := Real.exp (-2 * t)
    have hbinom :
        (1 + x) ^ (2 * n) =
          (∑ j ∈ range (2 * n + 1), (Nat.choose (2 * n) j : ℝ) * x ^ j) := by
      calc
        (1 + x) ^ (2 * n)
            = (x + 1) ^ (2 * n) := by rw [add_comm]
        _ = ∑ j ∈ range (2 * n + 1),
              x ^ j * 1 ^ (2 * n - j) * (Nat.choose (2 * n) j : ℝ) := by
              simpa using (add_pow x (1 : ℝ) (2 * n))
        _ = ∑ j ∈ range (2 * n + 1),
              (Nat.choose (2 * n) j : ℝ) * x ^ j := by
              refine sum_congr rfl ?_
              intro j _hj
              ring
    change
      5 * (∑ j ∈ range (2 * n + 1), (Nat.choose (2 * n) j : ℝ) * x ^ j) =
        5 * (1 + x) ^ (2 * n)
    rw [← hbinom]

end Omega.Zeta
