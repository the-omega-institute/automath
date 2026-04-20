import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-foldbin-gauge-entropy-one-nat-law`. -/
theorem paper_xi_foldbin_gauge_entropy_one_nat_law {X : Type} [Fintype X] (m : Nat)
    (mu d : X -> Real) (hmu : forall w, mu w = d w / (2 : Real) ^ m)
    (hprob : Finset.univ.sum mu = 1) (hpos : forall w, 0 < mu w) :
    Finset.univ.sum (fun w => mu w * Real.log (d w)) =
      (m : Real) * Real.log 2 - (-(Finset.univ.sum (fun w => mu w * Real.log (mu w)))) := by
  let c : Real := (m : Real) * Real.log 2
  have hpow_pos : 0 < (2 : Real) ^ m := by positivity
  have hpow_ne : (2 : Real) ^ m ≠ 0 := ne_of_gt hpow_pos
  have hlogd : ∀ w, Real.log (d w) = c + Real.log (mu w) := by
    intro w
    have hd_eq : d w = mu w * (2 : Real) ^ m := by
      have hm := congrArg (fun t => t * (2 : Real) ^ m) (hmu w)
      simpa [div_eq_mul_inv, mul_assoc, hpow_ne] using hm.symm
    rw [hd_eq, Real.log_mul (ne_of_gt (hpos w)) hpow_ne, Real.log_pow]
    simp [c, add_comm, add_left_comm, add_assoc]
  calc
    Finset.univ.sum (fun w => mu w * Real.log (d w))
        = Finset.univ.sum (fun w => mu w * (c + Real.log (mu w))) := by
            refine Finset.sum_congr rfl ?_
            intro w _
            rw [hlogd w]
    _ = Finset.univ.sum (fun w => mu w * c + mu w * Real.log (mu w)) := by
          refine Finset.sum_congr rfl ?_
          intro w _
          ring
    _ = Finset.univ.sum (fun w => mu w * c) + Finset.univ.sum (fun w => mu w * Real.log (mu w)) := by
          rw [Finset.sum_add_distrib]
    _ = c * Finset.univ.sum mu + Finset.univ.sum (fun w => mu w * Real.log (mu w)) := by
          congr 1
          rw [show (Finset.univ.sum fun w => mu w * c) = Finset.univ.sum fun w => c * mu w by
                refine Finset.sum_congr rfl ?_
                intro w _
                rw [mul_comm]]
          rw [← Finset.mul_sum]
    _ = c + Finset.univ.sum (fun w => mu w * Real.log (mu w)) := by
          rw [hprob, mul_one]
    _ = (m : Real) * Real.log 2 - (-(Finset.univ.sum (fun w => mu w * Real.log (mu w)))) := by
          simp [c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

end Omega.Zeta
