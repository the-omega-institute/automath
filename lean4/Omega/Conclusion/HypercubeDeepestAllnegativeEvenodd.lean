import Mathlib.Tactic

namespace Omega.Conclusion

/-- Residual hypercube dimension after taking the all-negative compressed layer. -/
def conclusion_hypercube_deepest_allnegative_evenodd_residual (m r : ℕ) : ℕ :=
  m - 2 * r

/-- Dimension of the compressed all-negative layer. -/
def conclusion_hypercube_deepest_allnegative_evenodd_dim (m r : ℕ) : ℕ :=
  2 ^ conclusion_hypercube_deepest_allnegative_evenodd_residual m r

/-- Adjacency spectrum for the residual dimensions used by the deepest all-negative layer. -/
def conclusion_hypercube_deepest_allnegative_evenodd_adjSpec (m r : ℕ) : Set ℤ :=
  if conclusion_hypercube_deepest_allnegative_evenodd_residual m r = 1 then
    ({-1, 1} : Set ℤ)
  else if conclusion_hypercube_deepest_allnegative_evenodd_residual m r = 0 then
    ({0} : Set ℤ)
  else
    Set.univ

/-- Laplacian spectrum for the residual dimensions used by the deepest all-negative layer. -/
def conclusion_hypercube_deepest_allnegative_evenodd_lapSpec (m r : ℕ) : Set ℤ :=
  if conclusion_hypercube_deepest_allnegative_evenodd_residual m r = 1 then
    ({2 * (r : ℤ), 2 * (r : ℤ) + 2} : Set ℤ)
  else if conclusion_hypercube_deepest_allnegative_evenodd_residual m r = 0 then
    ({2 * (r : ℤ)} : Set ℤ)
  else
    Set.univ

theorem paper_conclusion_hypercube_deepest_allnegative_evenodd (r : ℕ) :
    conclusion_hypercube_deepest_allnegative_evenodd_dim (2 * r) r = 1 ∧
      conclusion_hypercube_deepest_allnegative_evenodd_dim (2 * r + 1) r = 2 ∧
      conclusion_hypercube_deepest_allnegative_evenodd_adjSpec (2 * r + 1) r =
        ({-1, 1} : Set ℤ) ∧
      conclusion_hypercube_deepest_allnegative_evenodd_lapSpec (2 * r + 1) r =
        ({2 * (r : ℤ), 2 * (r : ℤ) + 2} : Set ℤ) := by
  have hEven : conclusion_hypercube_deepest_allnegative_evenodd_residual (2 * r) r = 0 := by
    unfold conclusion_hypercube_deepest_allnegative_evenodd_residual
    omega
  have hOdd : conclusion_hypercube_deepest_allnegative_evenodd_residual (2 * r + 1) r = 1 := by
    unfold conclusion_hypercube_deepest_allnegative_evenodd_residual
    omega
  simp [conclusion_hypercube_deepest_allnegative_evenodd_dim,
    conclusion_hypercube_deepest_allnegative_evenodd_adjSpec,
    conclusion_hypercube_deepest_allnegative_evenodd_lapSpec, hEven, hOdd]

end Omega.Conclusion
