import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

private theorem xiBulkEntropyRGLogTerm_hasDerivAt (delta : Real) (s : Real) (hdelta : 0 < delta) :
    HasDerivAt (fun u : Real => Real.log (1 + Real.exp u * delta))
      ((Real.exp s * delta) / (1 + Real.exp s * delta)) s := by
  have harg : HasDerivAt (fun u : Real => 1 + Real.exp u * delta) (Real.exp s * delta) s := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((Real.hasDerivAt_exp s).mul_const delta).const_add (1 : Real)
  have harg_ne : 1 + Real.exp s * delta ≠ 0 := by
    positivity
  simpa using harg.log harg_ne

/-- Paper label: `cor:xi-bulk-entropy-rg-staircase`. -/
theorem paper_xi_bulk_entropy_rg_staircase (k : Nat) (delta : Fin k → Real) (s : Real)
    (hdelta : ∀ j, 0 < delta j) :
    deriv
        (fun u : Real =>
          -((k : Real) * ((k : Real) - 1)) * u +
            (((2 : Real) * k - 1) * ∑ j : Fin k, Real.log (1 + Real.exp u * delta j)))
        s =
      (k : Real) ^ 2 - (((2 : Real) * k - 1) * ∑ j : Fin k, 1 / (1 + Real.exp s * delta j)) := by
  have hsum :
      HasDerivAt (fun u : Real => ∑ j : Fin k, Real.log (1 + Real.exp u * delta j))
        (∑ j : Fin k, (Real.exp s * delta j) / (1 + Real.exp s * delta j)) s := by
    simpa using
      (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin k))) fun j _ =>
        xiBulkEntropyRGLogTerm_hasDerivAt (delta j) s (hdelta j))
  have hlin :
      HasDerivAt (fun u : Real => -((k : Real) * ((k : Real) - 1)) * u)
        (-((k : Real) * ((k : Real) - 1))) s := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      HasDerivAt.const_mul (-((k : Real) * ((k : Real) - 1)) : Real) (hasDerivAt_id s)
  have hscaled :
      HasDerivAt
        (fun u : Real => (((2 : Real) * k - 1) * ∑ j : Fin k, Real.log (1 + Real.exp u * delta j)))
        ((((2 : Real) * k - 1) * ∑ j : Fin k, (Real.exp s * delta j) / (1 + Real.exp s * delta j)))
        s := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      HasDerivAt.const_mul (((2 : Real) * k - 1) : Real) hsum
  have hmain :
      HasDerivAt
        (fun u : Real =>
          -((k : Real) * ((k : Real) - 1)) * u +
            (((2 : Real) * k - 1) * ∑ j : Fin k, Real.log (1 + Real.exp u * delta j)))
        (-((k : Real) * ((k : Real) - 1)) +
          (((2 : Real) * k - 1) * ∑ j : Fin k, (Real.exp s * delta j) / (1 + Real.exp s * delta j)))
        s :=
    hlin.add hscaled
  rw [hmain.deriv]
  have hrewrite :
      (∑ j : Fin k, (Real.exp s * delta j) / (1 + Real.exp s * delta j)) =
        (k : Real) - ∑ j : Fin k, 1 / (1 + Real.exp s * delta j) := by
    calc
      ∑ j : Fin k, (Real.exp s * delta j) / (1 + Real.exp s * delta j) =
          ∑ j : Fin k, (1 - 1 / (1 + Real.exp s * delta j)) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            have hden_pos : 0 < 1 + Real.exp s * delta j := by
              have hterm_pos : 0 < Real.exp s * delta j := by
                exact mul_pos (Real.exp_pos s) (hdelta j)
              linarith
            have hden : 1 + Real.exp s * delta j ≠ 0 := hden_pos.ne'
            field_simp [hden]
            ring
      _ = (∑ _j : Fin k, (1 : Real)) - ∑ j : Fin k, 1 / (1 + Real.exp s * delta j) := by
            rw [Finset.sum_sub_distrib]
      _ = (k : Real) - ∑ j : Fin k, 1 / (1 + Real.exp s * delta j) := by simp
  rw [hrewrite]
  ring

end Omega.Zeta
