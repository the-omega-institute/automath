import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace Omega.Zeta

open Finset

/-- The adjacency eigenvalue contributed by the `j`-th Hamming layer of `Q_(2n)`. -/
def leyangBranchsetEigenvalue (n j : ℕ) : ℤ := (2 * n : ℤ) - 2 * j

/-- Five disjoint copies of `Q_(2n)` multiply each hypercube multiplicity by `5`. -/
def leyangBranchsetMultiplicity (n j : ℕ) : ℕ := 5 * Nat.choose (2 * n) j

/-- The heat trace obtained by summing `exp (t * λ)` over the hypercube spectrum. -/
noncomputable def leyangBranchsetHeatTrace (n : ℕ) (t : ℝ) : ℝ :=
  5 * Finset.sum (Finset.range (2 * n + 1)) fun j =>
    (Nat.choose (2 * n) j : ℝ) * Real.exp (t * (((2 * n : ℕ) : ℝ) - 2 * (j : ℝ)))

lemma leyang_heat_trace_term (n j : ℕ) (t : ℝ) (hj : j ∈ Finset.range (2 * n + 1)) :
    (Nat.choose (2 * n) j : ℝ) * Real.exp (t * (((2 * n : ℕ) : ℝ) - 2 * (j : ℝ))) =
      Real.exp (-t) ^ j * Real.exp t ^ (2 * n - j) * (Nat.choose (2 * n) j : ℝ) := by
  have hj' : j ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow :
      Real.exp (t * (((2 * n : ℕ) : ℝ) - 2 * (j : ℝ))) =
        Real.exp (-t) ^ j * Real.exp t ^ (2 * n - j) := by
    rw [← Real.exp_nat_mul (-t) j, ← Real.exp_nat_mul t (2 * n - j), ← Real.exp_add]
    have hsub1 : ((2 * n - j : ℕ) : ℝ) = (((2 * n : ℕ) : ℝ) - (j : ℝ)) := by
      exact Nat.cast_sub hj'
    rw [hsub1]
    ring_nf
  calc
    (Nat.choose (2 * n) j : ℝ) * Real.exp (t * (((2 * n : ℕ) : ℝ) - 2 * (j : ℝ))) =
        (Nat.choose (2 * n) j : ℝ) * (Real.exp (-t) ^ j * Real.exp t ^ (2 * n - j)) := by
          rw [hpow]
    _ = Real.exp (-t) ^ j * Real.exp t ^ (2 * n - j) * (Nat.choose (2 * n) j : ℝ) := by ring

lemma leyang_heat_trace_closed_form (n : ℕ) (t : ℝ) :
    leyangBranchsetHeatTrace n t = 5 * (2 * Real.cosh t) ^ (2 * n) := by
  have hsum :
      Finset.sum (Finset.range (2 * n + 1)) (fun j =>
        (Nat.choose (2 * n) j : ℝ) * Real.exp (t * (((2 * n : ℕ) : ℝ) - 2 * (j : ℝ)))) =
          (Real.exp (-t) + Real.exp t) ^ (2 * n) := by
    calc
      _ = Finset.sum (Finset.range (2 * n + 1)) (fun j =>
            Real.exp (-t) ^ j * Real.exp t ^ (2 * n - j) * (Nat.choose (2 * n) j : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              exact leyang_heat_trace_term n j t hj
      _ = (Real.exp (-t) + Real.exp t) ^ (2 * n) := by
            symm
            simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
              add_pow (Real.exp (-t)) (Real.exp t) (2 * n)
  have hcosh : Real.exp (-t) + Real.exp t = 2 * Real.cosh t := by
    rw [Real.cosh_eq]
    ring
  rw [leyangBranchsetHeatTrace, hsum, hcosh]

end Omega.Zeta

/-- Paper-facing Lee--Yang branchset package: five copies of `Q_(2n)` give the hypercube
eigenvalues `2n - 2j` with multiplicity `5 * choose (2n) j`, and summing `exp (t * λ)` over that
spectrum yields the closed heat-trace form `5 * (2 * cosh t)^(2n)`.
    thm:derived-leyang-branchset-adjacency-spectrum-heat-trace -/
theorem paper_derived_leyang_branchset_adjacency_spectrum_heat_trace (n : ℕ) (t : ℝ) :
    (∀ j ∈ Finset.range (2 * n + 1),
      Omega.Zeta.leyangBranchsetEigenvalue n j = (2 * n : ℤ) - 2 * j ∧
        Omega.Zeta.leyangBranchsetMultiplicity n j = 5 * Nat.choose (2 * n) j) ∧
      Omega.Zeta.leyangBranchsetHeatTrace n t = 5 * (2 * Real.cosh t) ^ (2 * n) := by
  refine ⟨?_, Omega.Zeta.leyang_heat_trace_closed_form n t⟩
  intro j hj
  let _ := hj
  simp [Omega.Zeta.leyangBranchsetEigenvalue, Omega.Zeta.leyangBranchsetMultiplicity]
