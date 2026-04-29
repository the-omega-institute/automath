import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-foldbin-entropy-gauge-one-nat-gap`. -/
theorem paper_xi_foldbin_entropy_gauge_one_nat_gap {α : Type*} [Fintype α] [DecidableEq α]
    (m : Nat) (d : α -> Nat) (kappa entropy : Real) (hpos : ∀ w, 0 < d w)
    (h_mass : (Finset.univ.sum fun w => (d w : Real)) = (2 : Real) ^ m)
    (h_kappa :
      kappa = (Finset.univ.sum fun w => (d w : Real) * Real.log (d w)) / (2 : Real) ^ m)
    (h_entropy :
      entropy =
        - (Finset.univ.sum fun w =>
          ((d w : Real) / (2 : Real) ^ m) *
            Real.log ((d w : Real) / (2 : Real) ^ m))) :
    entropy = (m : Real) * Real.log 2 - kappa := by
  let mu : α → ℝ := fun w => (d w : ℝ) / (2 : ℝ) ^ m
  have hpow_pos : 0 < (2 : ℝ) ^ m := by positivity
  have hpow_ne : (2 : ℝ) ^ m ≠ 0 := hpow_pos.ne'
  have hmu_pos : ∀ w, 0 < mu w := by
    intro w
    exact div_pos (by exact_mod_cast hpos w) hpow_pos
  let c : ℝ := (m : ℝ) * Real.log 2
  have hlogd : ∀ w, Real.log ((d w : ℝ)) = c + Real.log (mu w) := by
    intro w
    have hd_eq : (d w : ℝ) = mu w * (2 : ℝ) ^ m := by
      dsimp [mu]
      field_simp [hpow_ne]
    rw [hd_eq, Real.log_mul (hmu_pos w).ne' hpow_ne, Real.log_pow]
    simp [c, add_comm]
  have hmu_sum : Finset.univ.sum mu = 1 := by
    dsimp [mu]
    calc
      (Finset.univ.sum fun w => (d w : ℝ) / (2 : ℝ) ^ m)
          = (Finset.univ.sum fun w => (d w : ℝ)) / (2 : ℝ) ^ m := by
              rw [Finset.sum_div]
      _ = 1 := by
        rw [h_mass]
        field_simp [hpow_ne]
  have hidentity :
      Finset.univ.sum (fun w => mu w * Real.log ((d w : ℝ))) =
        (m : ℝ) * Real.log 2 -
          (-(Finset.univ.sum fun w => mu w * Real.log (mu w))) := by
    calc
      Finset.univ.sum (fun w => mu w * Real.log ((d w : ℝ)))
          = Finset.univ.sum (fun w => mu w * (c + Real.log (mu w))) := by
              refine Finset.sum_congr rfl ?_
              intro w _hw
              rw [hlogd w]
      _ = Finset.univ.sum (fun w => mu w * c + mu w * Real.log (mu w)) := by
            refine Finset.sum_congr rfl ?_
            intro w _hw
            ring
      _ = Finset.univ.sum (fun w => mu w * c) +
            Finset.univ.sum (fun w => mu w * Real.log (mu w)) := by
            rw [Finset.sum_add_distrib]
      _ = c * Finset.univ.sum mu +
            Finset.univ.sum (fun w => mu w * Real.log (mu w)) := by
            congr 1
            rw [show (Finset.univ.sum fun w => mu w * c) =
                Finset.univ.sum fun w => c * mu w by
              refine Finset.sum_congr rfl ?_
              intro w _hw
              rw [mul_comm]]
            rw [← Finset.mul_sum]
      _ = c + Finset.univ.sum (fun w => mu w * Real.log (mu w)) := by
            rw [hmu_sum, mul_one]
      _ = (m : ℝ) * Real.log 2 -
            (-(Finset.univ.sum fun w => mu w * Real.log (mu w))) := by
            simp [c, sub_eq_add_neg]
  have hkappa_mu :
      kappa = Finset.univ.sum (fun w => mu w * Real.log ((d w : ℝ))) := by
    calc
      kappa = (Finset.univ.sum fun w => (d w : ℝ) * Real.log (d w)) / (2 : ℝ) ^ m :=
        h_kappa
      _ = Finset.univ.sum (fun w => ((d w : ℝ) * Real.log (d w)) / (2 : ℝ) ^ m) := by
        rw [Finset.sum_div]
      _ = Finset.univ.sum (fun w => mu w * Real.log ((d w : ℝ))) := by
        refine Finset.sum_congr rfl ?_
        intro w _hw
        dsimp [mu]
        ring
  have hkappa_entropy : kappa = (m : ℝ) * Real.log 2 - entropy := by
    rw [hkappa_mu, h_entropy]
    exact hidentity
  linarith

end Omega.Zeta
