import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private theorem xiBulkBoundaryLogTerm_eq (δ u : Real) (hδ : 0 < δ) :
    Real.log ((1 + Real.exp u * δ) / (Real.exp u * (1 + δ))) =
      Real.log ((Real.exp (-u) + δ) / (1 + δ)) := by
  have hden : 1 + δ ≠ 0 := by linarith
  have hexp : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  congr 1
  calc
    (1 + Real.exp u * δ) / (Real.exp u * (1 + δ)) =
        (Real.exp u * (Real.exp (-u) + δ)) / (Real.exp u * (1 + δ)) := by
          have hnum : Real.exp u * (Real.exp (-u) + δ) = 1 + Real.exp u * δ := by
            rw [mul_add, hexp]
          rw [hnum]
    _ = (Real.exp (-u) + δ) / (1 + δ) := by
          field_simp [Real.exp_ne_zero u, hden]

private theorem xiBulkBoundaryLogTerm_hasDerivAt (delta : Real) (s : Real) (hdelta : 0 < delta) :
    HasDerivAt (fun u : Real => Real.log ((Real.exp (-u) + delta) / (1 + delta)))
      (-(1 / (1 + Real.exp s * delta))) s := by
  have harg :
      HasDerivAt (fun u : Real => (Real.exp (-u) + delta) / (1 + delta))
        ((-Real.exp (-s)) / (1 + delta)) s := by
    simpa [add_comm] using
      ((((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)).const_add delta).div_const
        (1 + delta))
  have harg_ne : (Real.exp (-s) + delta) / (1 + delta) ≠ 0 := by
    have harg_pos : 0 < (Real.exp (-s) + delta) / (1 + delta) := by
      positivity
    exact harg_pos.ne'
  convert harg.log harg_ne using 1
  have hden : 1 + delta ≠ 0 := by linarith
  have hexp : Real.exp s ≠ 0 := by exact Real.exp_ne_zero s
  have hexp_mul : Real.exp (-s) * Real.exp s = 1 := by
    rw [← Real.exp_add]
    simp
  have hexp_mul' : Real.exp s * Real.exp (-s) = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp [hden, hexp]
  have hmul : Real.exp (-s) + delta = (1 + Real.exp s * delta) * Real.exp (-s) := by
    calc
      Real.exp (-s) + delta = Real.exp (-s) + (Real.exp s * Real.exp (-s)) * delta := by
        rw [hexp_mul']
        ring
      _ = (1 + Real.exp s * delta) * Real.exp (-s) := by
        ring
  linarith

/-- Paper label: `cor:xi-bulk-boundary-holographic-gap-dissipation`. -/
theorem paper_xi_bulk_boundary_holographic_gap_dissipation (k : Nat) (delta : Fin k → Real)
    (s : Real) (hdelta : ∀ j, 0 < delta j) :
    deriv
        (fun u : Real =>
          (((2 : Real) * k - 1) *
            ∑ j : Fin k, Real.log ((1 + Real.exp u * delta j) / (Real.exp u * (1 + delta j)))))
        s =
      -(((2 : Real) * k - 1) * ∑ j : Fin k, 1 / (1 + Real.exp s * delta j)) := by
  rw [show
      (fun u : Real =>
        (((2 : Real) * k - 1) *
          ∑ j : Fin k, Real.log ((1 + Real.exp u * delta j) / (Real.exp u * (1 + delta j))))) =
        (fun u : Real =>
          (((2 : Real) * k - 1) *
            ∑ j : Fin k, Real.log ((Real.exp (-u) + delta j) / (1 + delta j)))) by
      funext u
      congr 1
      exact Finset.sum_congr rfl (fun j _ => xiBulkBoundaryLogTerm_eq (delta j) u (hdelta j))]
  have hsum :
      HasDerivAt
        (fun u : Real => ∑ j : Fin k, Real.log ((Real.exp (-u) + delta j) / (1 + delta j)))
        (∑ j : Fin k, -(1 / (1 + Real.exp s * delta j))) s := by
    simpa using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin k))) fun j _ =>
        xiBulkBoundaryLogTerm_hasDerivAt (delta j) s (hdelta j))
  have hmain :
      HasDerivAt
        (fun u : Real =>
          (((2 : Real) * k - 1) *
            ∑ j : Fin k, Real.log ((Real.exp (-u) + delta j) / (1 + delta j))))
        ((((2 : Real) * k - 1) * ∑ j : Fin k, -(1 / (1 + Real.exp s * delta j)))) s := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      HasDerivAt.const_mul (((2 : Real) * k - 1) : Real) hsum
  rw [hmain.deriv]
  have hneg :
      (∑ j : Fin k, -(1 / (1 + Real.exp s * delta j))) =
        -∑ j : Fin k, 1 / (1 + Real.exp s * delta j) := by
    simp
  rw [hneg]
  ring

end Omega.Zeta
