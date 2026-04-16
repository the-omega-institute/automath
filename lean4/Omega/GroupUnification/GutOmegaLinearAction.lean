import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.GroupUnification

set_option maxHeartbeats 400000 in
/-- Summing the affine logarithmic model for `d_m` linearizes the total information cost over the
selector set `Sigma`.
    prop:gut-omega-linear-action -/
theorem paper_gut_omega_linear_action (d : Nat -> Real) (Sigma : Finset Nat) (c0 c1 : Real)
    (hlog : ∀ m ∈ Sigma, Real.log (d m) = c1 * (m : Real) + c0) :
    Finset.sum Sigma (fun m => Real.log (d m)) =
      c1 * Finset.sum Sigma (fun m => (m : Real)) + c0 * (Sigma.card : Real) := by
  calc
    Finset.sum Sigma (fun m => Real.log (d m)) = Finset.sum Sigma (fun m => c1 * (m : Real) + c0) := by
      refine Finset.sum_congr rfl ?_
      intro m hm
      exact hlog m hm
    _ = Finset.sum Sigma (fun m => c1 * (m : Real)) + Finset.sum Sigma (fun _ => c0) := by
      rw [Finset.sum_add_distrib]
    _ = c1 * Finset.sum Sigma (fun m => (m : Real)) + (Sigma.card : Real) * c0 := by
      rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ = c1 * Finset.sum Sigma (fun m => (m : Real)) + c0 * (Sigma.card : Real) := by
      ring

end Omega.GroupUnification
