import Mathlib

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The explicit increment used in the toy Lambert-W recursion. -/
def lambertWDrift (c : ℝ) (n : ℕ) : ℝ :=
  c / (n + 1)

/-- Recursive trajectory obtained by adding the explicit drift at each step. -/
def lambertWRecursiveTrajectory (c u0 : ℝ) : ℕ → ℝ
  | 0 => u0
  | n + 1 => lambertWRecursiveTrajectory c u0 n + lambertWDrift c n

/-- Closed-form trajectory obtained by summing the same drifts. -/
def lambertWReferenceTrajectory (c u0 : ℝ) (n : ℕ) : ℝ :=
  u0 + Finset.sum (Finset.range n) (fun k => lambertWDrift c k)

/-- Pointwise trajectory error between the recursive and reference evolutions. -/
def lambertWTrajectoryError (c u0 : ℝ) (n : ℕ) : ℝ :=
  |lambertWRecursiveTrajectory c u0 n - lambertWReferenceTrajectory c u0 n|

lemma lambertWRecursiveTrajectory_eq_reference (c u0 : ℝ) :
    ∀ n, lambertWRecursiveTrajectory c u0 n = lambertWReferenceTrajectory c u0 n
  | 0 => by simp [lambertWRecursiveTrajectory, lambertWReferenceTrajectory]
  | n + 1 => by
      calc
        lambertWRecursiveTrajectory c u0 (n + 1)
            = lambertWRecursiveTrajectory c u0 n + lambertWDrift c n := by
                rw [lambertWRecursiveTrajectory]
        _ = lambertWReferenceTrajectory c u0 n + lambertWDrift c n := by
              rw [lambertWRecursiveTrajectory_eq_reference]
        _ = lambertWReferenceTrajectory c u0 (n + 1) := by
              simp [lambertWReferenceTrajectory, Finset.sum_range_succ, add_assoc]

lemma lambertWRecursiveTrajectory_increment (c u0 : ℝ) (n : ℕ) :
    lambertWRecursiveTrajectory c u0 (n + 1) - lambertWRecursiveTrajectory c u0 n =
      lambertWDrift c n := by
  rw [lambertWRecursiveTrajectory]
  ring

lemma lambertWRecursiveTrajectory_difference (c u0 v0 : ℝ) :
    ∀ n,
      lambertWRecursiveTrajectory c u0 n - lambertWRecursiveTrajectory c v0 n = u0 - v0
  | 0 => by simp [lambertWRecursiveTrajectory]
  | n + 1 => by
      calc
        lambertWRecursiveTrajectory c u0 (n + 1) - lambertWRecursiveTrajectory c v0 (n + 1)
            = (lambertWRecursiveTrajectory c u0 n + lambertWDrift c n) -
                (lambertWRecursiveTrajectory c v0 n + lambertWDrift c n) := by
                  rw [lambertWRecursiveTrajectory, lambertWRecursiveTrajectory]
        _ = lambertWRecursiveTrajectory c u0 n - lambertWRecursiveTrajectory c v0 n := by ring
        _ = u0 - v0 := lambertWRecursiveTrajectory_difference c u0 v0 n

/-- Paper label: `prop:xi-lambertW-recursive-trajectory-stability`.
In the concrete recursion with explicit drift `c / (n + 1)`, the recursive orbit agrees exactly
with the summed reference trajectory, the one-step defect is the prescribed drift, and any initial
error bound propagates uniformly along the whole trajectory. -/
theorem paper_xi_lambertw_recursive_trajectory_stability (c u0 v0 ε : ℝ)
    (hε : |u0 - v0| ≤ ε) :
    (∀ n, lambertWRecursiveTrajectory c u0 n = lambertWReferenceTrajectory c u0 n) ∧
      (∀ n,
        lambertWRecursiveTrajectory c u0 (n + 1) - lambertWRecursiveTrajectory c u0 n =
          lambertWDrift c n) ∧
      (∀ n,
        |lambertWRecursiveTrajectory c u0 n - lambertWRecursiveTrajectory c v0 n| ≤ ε) ∧
      (∀ n, lambertWTrajectoryError c u0 n = 0) := by
  refine ⟨lambertWRecursiveTrajectory_eq_reference c u0, ?_, ?_, ?_⟩
  · intro n
    exact lambertWRecursiveTrajectory_increment c u0 n
  · intro n
    rw [abs_le]
    have hdiff := lambertWRecursiveTrajectory_difference c u0 v0 n
    have habs : -ε ≤ u0 - v0 ∧ u0 - v0 ≤ ε := by
      simpa using abs_le.mp hε
    constructor
    · rw [hdiff]
      exact habs.1
    · rw [hdiff]
      exact habs.2
  · intro n
    rw [lambertWTrajectoryError, abs_eq_zero]
    exact sub_eq_zero.mpr (lambertWRecursiveTrajectory_eq_reference c u0 n)

end

end Omega.Zeta
