import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.SyncKernelWeighted.AdditionCollisionHoelderLowerBound

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The real-input instantiation of the boundary/bulk Hölder package uses entropy rates
`2 log φ` for `X_m × X_m` and `log 2` for the free binary output boundary. -/
def addition_collision_real_hoelder_lb_data (q : ℕ) : AdditionCollisionHoelderData where
  q := q
  inputCard := 1
  outputCard := 1
  hIn := 2 * Real.log Real.goldenRatio
  hOut := Real.log 2

/-- The simplified real-input lower-bound exponent. -/
def addition_collision_real_hoelder_lb_value (q : ℕ) : ℝ :=
  Real.goldenRatio ^ (2 * q) / (2 : ℝ) ^ (q - 1)

lemma addition_collision_real_hoelder_lb_exponential_form (q : ℕ) (hq : 1 ≤ q) :
    Real.exp
        (((q : ℝ) * (2 * Real.log Real.goldenRatio)) -
          (((q : ℝ) - 1) * Real.log 2)) =
      addition_collision_real_hoelder_lb_value q := by
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have htwo_pos : 0 < (2 : ℝ) := by norm_num
  have hq_sub : ((q : ℝ) - 1) = ((q - 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_sub hq]
  have hmul :
      (q : ℝ) * (2 * Real.log Real.goldenRatio) =
        (((2 * q : ℕ) : ℝ) * Real.log Real.goldenRatio) := by
    norm_num [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
  calc
    Real.exp
        (((q : ℝ) * (2 * Real.log Real.goldenRatio)) -
          (((q : ℝ) - 1) * Real.log 2)) =
      Real.exp ((((2 * q : ℕ) : ℝ) * Real.log Real.goldenRatio) -
        (((q - 1 : ℕ) : ℝ) * Real.log 2)) := by
          rw [hq_sub, hmul]
    _ =
        Real.exp (((2 * q : ℕ) : ℝ) * Real.log Real.goldenRatio) *
          Real.exp (-(((q - 1 : ℕ) : ℝ) * Real.log 2)) := by
            rw [sub_eq_add_neg, Real.exp_add]
    _ = Real.goldenRatio ^ (2 * q) * (((2 : ℝ) ^ (q - 1))⁻¹) := by
          rw [Real.exp_nat_mul, Real.exp_log hphi_pos, Real.exp_neg,
            Real.exp_nat_mul, Real.exp_log htwo_pos]
    _ = addition_collision_real_hoelder_lb_value q := by
          simp [addition_collision_real_hoelder_lb_value, div_eq_mul_inv]

/-- Paper label: `cor:addition-collision-real-hoelder-lb`. The real-input specialization of the
existing boundary/bulk Hölder lower bound yields the exponent `φ^(2q) / 2^(q-1)`; the `q = 2`
case is the direct specialization `φ^4 / 2`. -/
theorem paper_addition_collision_real_hoelder_lb (q : ℕ) (hq : 1 ≤ q) :
    (addition_collision_real_hoelder_lb_data q).rq ≥ addition_collision_real_hoelder_lb_value q ∧
      (addition_collision_real_hoelder_lb_data 2).rq ≥ Real.goldenRatio ^ (4 : ℕ) / 2 := by
  have hMainRaw :
      (addition_collision_real_hoelder_lb_data q).rq ≥
        Real.exp
          (((q : ℝ) * (addition_collision_real_hoelder_lb_data q).hIn) -
            (((q : ℝ) - 1) * (addition_collision_real_hoelder_lb_data q).hOut)) :=
    (paper_addition_collision_hoelder_lb_boundary_bulk
      (addition_collision_real_hoelder_lb_data q)).2
  have hMain :
      (addition_collision_real_hoelder_lb_data q).rq ≥ addition_collision_real_hoelder_lb_value q := by
    calc
      (addition_collision_real_hoelder_lb_data q).rq ≥
          Real.exp
            (((q : ℝ) * (addition_collision_real_hoelder_lb_data q).hIn) -
              (((q : ℝ) - 1) * (addition_collision_real_hoelder_lb_data q).hOut)) :=
        hMainRaw
      _ = addition_collision_real_hoelder_lb_value q := by
          simpa [addition_collision_real_hoelder_lb_data] using
            addition_collision_real_hoelder_lb_exponential_form q hq
  have hTwoRaw :
      (addition_collision_real_hoelder_lb_data 2).rq ≥
        Real.exp
          (((2 : ℝ) * (addition_collision_real_hoelder_lb_data 2).hIn) -
            (((2 : ℝ) - 1) * (addition_collision_real_hoelder_lb_data 2).hOut)) :=
    (paper_addition_collision_hoelder_lb_boundary_bulk
      (addition_collision_real_hoelder_lb_data 2)).2
  have hTwo :
      (addition_collision_real_hoelder_lb_data 2).rq ≥ Real.goldenRatio ^ (4 : ℕ) / 2 := by
    calc
      (addition_collision_real_hoelder_lb_data 2).rq ≥
          Real.exp
            (((2 : ℝ) * (addition_collision_real_hoelder_lb_data 2).hIn) -
              (((2 : ℝ) - 1) * (addition_collision_real_hoelder_lb_data 2).hOut)) :=
        hTwoRaw
      _ = addition_collision_real_hoelder_lb_value 2 := by
          simpa [addition_collision_real_hoelder_lb_data] using
            addition_collision_real_hoelder_lb_exponential_form 2 (by norm_num)
      _ = Real.goldenRatio ^ (4 : ℕ) / 2 := by
          simp [addition_collision_real_hoelder_lb_value]
  exact ⟨hMain, hTwo⟩

end

end Omega.SyncKernelWeighted
