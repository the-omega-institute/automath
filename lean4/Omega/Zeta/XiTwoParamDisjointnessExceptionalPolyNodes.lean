import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `thm:xi-two-param-disjointness-exceptional-poly-nodes`. -/
theorem paper_xi_two_param_disjointness_exceptional_poly_nodes (q : Nat) (d b : ℝ)
    (w mu : Fin (q + 1) → ℝ) (P : ℝ → ℝ)
    (hP : ∀ lam,
      P lam =
        (∏ i : Fin (q + 1), (lam - d * mu i)) -
          b * ∑ i : Fin (q + 1),
            w i * ∏ j : {j : Fin (q + 1) // j ≠ i}, (lam - d * mu j.1)) :
    ∀ i : Fin (q + 1),
      P (d * mu i) =
        -b * w i * ∏ j : {j : Fin (q + 1) // j ≠ i},
          (d * mu i - d * mu j.1) := by
  classical
  intro i
  have hfull :
      (∏ r : Fin (q + 1), (d * mu i - d * mu r)) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hsum :
      (∑ r : Fin (q + 1),
          w r * ∏ j : {j : Fin (q + 1) // j ≠ r},
            (d * mu i - d * mu j.1)) =
        w i * ∏ j : {j : Fin (q + 1) // j ≠ i}, (d * mu i - d * mu j.1) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro r _hr hri
      have hzero :
          (∏ j : {j : Fin (q + 1) // j ≠ r}, (d * mu i - d * mu j.1)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨i, hri.symm⟩) ?_
        simp
      simp [hzero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hP, hfull, hsum]
  ring

end Omega.Zeta
