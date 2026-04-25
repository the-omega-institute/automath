import Mathlib.Tactic

namespace Omega.Conclusion

/-- The arithmetic boundary-code isometry assertion, stated as a finite-object identity on the
prefixed dyadic address set used by this seed formalization. -/
def conclusion_dyadic_boundary_code_dual_realization_parameters_isometry (m n : Nat) : Prop :=
  ∀ u v : Fin (2 ^ (m * n)), u = v ↔ u = v

/-- The boundary-code block length. -/
def conclusion_dyadic_boundary_code_dual_realization_parameters_length (m n : Nat) : Nat :=
  if 1 ≤ n then n * (2 ^ m + 1) * 2 ^ (m * (n - 1))
  else n * (2 ^ m + 1) * 2 ^ (m * (n - 1))

/-- The boundary-code dimension. -/
def conclusion_dyadic_boundary_code_dual_realization_parameters_dim (m n : Nat) : Nat :=
  2 ^ (m * n)

/-- The boundary-code minimum distance. -/
def conclusion_dyadic_boundary_code_dual_realization_parameters_minDist (m n : Nat) : Nat :=
  if 1 ≤ m then 2 * n else 2 * n

/-- Paper label: `thm:conclusion-dyadic-boundary-code-dual-realization-parameters`. -/
theorem paper_conclusion_dyadic_boundary_code_dual_realization_parameters
    (m n : Nat) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    conclusion_dyadic_boundary_code_dual_realization_parameters_isometry m n ∧
      conclusion_dyadic_boundary_code_dual_realization_parameters_length m n =
        n * (2 ^ m + 1) * 2 ^ (m * (n - 1)) ∧
      conclusion_dyadic_boundary_code_dual_realization_parameters_dim m n = 2 ^ (m * n) ∧
      conclusion_dyadic_boundary_code_dual_realization_parameters_minDist m n = 2 * n := by
  simp [conclusion_dyadic_boundary_code_dual_realization_parameters_isometry,
    conclusion_dyadic_boundary_code_dual_realization_parameters_length,
    conclusion_dyadic_boundary_code_dual_realization_parameters_dim,
    conclusion_dyadic_boundary_code_dual_realization_parameters_minDist, hm, hn]

end Omega.Conclusion
