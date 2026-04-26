import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

noncomputable section

/-- Paper label: `prop:gm-nonresonant-exp-sum-curvature`. -/
theorem paper_gm_nonresonant_exp_sum_curvature (S : Nat -> Real -> Complex)
    (lambda dist : Real -> Real) (C c lambda0 : Real) (hC : 0 <= C) (_hlambda0 : 0 < lambda0)
    (hlambda_pos : forall theta, 0 < lambda theta) (_hc : 0 < c)
    (hperron : forall m theta, ‖S m theta‖ <= C * (lambda theta)^m)
    (hcurv : forall theta, Real.log (lambda theta) <= Real.log lambda0 - c * (dist theta)^2) :
    forall m theta,
      ‖S m theta‖ <=
        C * Real.exp ((m : Real) * (Real.log lambda0 - c * (dist theta)^2)) := by
  intro m theta
  have hpow_exp :
      Real.exp ((m : Real) * Real.log (lambda theta)) = (lambda theta) ^ m := by
    induction m with
    | zero =>
        simp
    | succ m ih =>
        calc
          Real.exp (((Nat.succ m : Nat) : Real) * Real.log (lambda theta))
              = Real.exp ((m : Real) * Real.log (lambda theta) + Real.log (lambda theta)) := by
                congr 1
                norm_num [Nat.cast_succ]
                ring
          _ = Real.exp ((m : Real) * Real.log (lambda theta)) *
                Real.exp (Real.log (lambda theta)) := by
                rw [Real.exp_add]
          _ = (lambda theta) ^ m * lambda theta := by
                rw [ih, Real.exp_log (hlambda_pos theta)]
          _ = (lambda theta) ^ Nat.succ m := by
                rw [pow_succ]
  have hlog_mul :
      (m : Real) * Real.log (lambda theta) <=
        (m : Real) * (Real.log lambda0 - c * (dist theta)^2) :=
    mul_le_mul_of_nonneg_left (hcurv theta) (Nat.cast_nonneg m)
  have hpow_le :
      (lambda theta) ^ m <=
        Real.exp ((m : Real) * (Real.log lambda0 - c * (dist theta)^2)) := by
    rw [<- hpow_exp]
    exact Real.exp_le_exp.mpr hlog_mul
  exact le_trans (hperron m theta) (mul_le_mul_of_nonneg_left hpow_le hC)

end
end Omega.SyncKernelRealInput
