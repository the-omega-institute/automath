import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The golden ratio parameter appearing in the neutralization recursion. -/
noncomputable def conclusion_golden_radius_neutralization_multiplicative_recursion_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- The exponential neutralization constant from the paper. -/
noncomputable def conclusion_golden_radius_neutralization_multiplicative_recursion_r (k : ℕ) : ℝ :=
  Real.exp
    (-(2 / Real.sqrt 5) *
      conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k)

/-- The multiplicative Fibonacci recursion for the neutralization constants. -/
def conclusion_golden_radius_neutralization_multiplicative_recursion_multiplicative_fibonacci_recursion :
    Prop :=
  ∀ k : ℕ,
    conclusion_golden_radius_neutralization_multiplicative_recursion_r (k + 2) =
      conclusion_golden_radius_neutralization_multiplicative_recursion_r (k + 1) *
        conclusion_golden_radius_neutralization_multiplicative_recursion_r k

/-- The golden-power recursion for the neutralization constants. -/
def conclusion_golden_radius_neutralization_multiplicative_recursion_golden_power_recursion :
    Prop :=
  ∀ k : ℕ,
    conclusion_golden_radius_neutralization_multiplicative_recursion_r (k + 1) =
      Real.rpow
        (conclusion_golden_radius_neutralization_multiplicative_recursion_r k)
        conclusion_golden_radius_neutralization_multiplicative_recursion_phi

private lemma conclusion_golden_radius_neutralization_multiplicative_recursion_phi_sq :
    conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ 2 =
      conclusion_golden_radius_neutralization_multiplicative_recursion_phi + 1 := by
  unfold conclusion_golden_radius_neutralization_multiplicative_recursion_phi
  have hsqrt : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by positivity)]
  field_simp
  nlinarith

private lemma conclusion_golden_radius_neutralization_multiplicative_recursion_phi_pow_add
    (k : ℕ) :
    conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ (k + 2) =
      conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ (k + 1) +
        conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k := by
  calc
    conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ (k + 2) =
        conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k *
          conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ 2 := by
      rw [pow_add]
    _ =
        conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k *
          (conclusion_golden_radius_neutralization_multiplicative_recursion_phi + 1) := by
      rw [conclusion_golden_radius_neutralization_multiplicative_recursion_phi_sq]
    _ =
        conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k *
          conclusion_golden_radius_neutralization_multiplicative_recursion_phi +
            conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k := by
      ring
    _ =
        conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ (k + 1) +
          conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k := by
      rw [pow_succ]

/-- Paper label: `cor:conclusion-golden-radius-neutralization-multiplicative-recursion`. -/
theorem paper_conclusion_golden_radius_neutralization_multiplicative_recursion :
    conclusion_golden_radius_neutralization_multiplicative_recursion_multiplicative_fibonacci_recursion ∧
      conclusion_golden_radius_neutralization_multiplicative_recursion_golden_power_recursion := by
  refine ⟨?_, ?_⟩
  · intro k
    calc
      conclusion_golden_radius_neutralization_multiplicative_recursion_r (k + 2) =
          Real.exp
            (-(2 / Real.sqrt 5) *
              (conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ (k + 1) +
                conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k)) := by
        rw [conclusion_golden_radius_neutralization_multiplicative_recursion_r,
          conclusion_golden_radius_neutralization_multiplicative_recursion_phi_pow_add]
      _ =
          Real.exp
              (-(2 / Real.sqrt 5) *
                conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ (k + 1) +
                -(2 / Real.sqrt 5) *
                  conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k) := by
        congr 1
        ring
      _ =
          Real.exp
              (-(2 / Real.sqrt 5) *
                conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ (k + 1)) *
            Real.exp
              (-(2 / Real.sqrt 5) *
                conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k) := by
        rw [Real.exp_add]
      _ =
          conclusion_golden_radius_neutralization_multiplicative_recursion_r (k + 1) *
            conclusion_golden_radius_neutralization_multiplicative_recursion_r k := by
        simp [conclusion_golden_radius_neutralization_multiplicative_recursion_r]
  · intro k
    calc
      conclusion_golden_radius_neutralization_multiplicative_recursion_r (k + 1) =
          Real.exp
            (-(2 / Real.sqrt 5) *
              conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ (k + 1)) := by
        rw [conclusion_golden_radius_neutralization_multiplicative_recursion_r]
      _ =
          Real.exp
            ((-(2 / Real.sqrt 5) *
                conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k) *
              conclusion_golden_radius_neutralization_multiplicative_recursion_phi) := by
        congr 1
        rw [pow_succ]
        ring
      _ =
          Real.exp
            (Real.log
                (Real.exp
                  (-(2 / Real.sqrt 5) *
                    conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k)) *
              conclusion_golden_radius_neutralization_multiplicative_recursion_phi) := by
        congr 1
        rw [Real.log_exp]
      _ =
          Real.rpow
            (Real.exp
              (-(2 / Real.sqrt 5) *
                conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k))
            conclusion_golden_radius_neutralization_multiplicative_recursion_phi := by
        symm
        exact
          Real.rpow_def_of_pos (x := Real.exp
            (-(2 / Real.sqrt 5) *
              conclusion_golden_radius_neutralization_multiplicative_recursion_phi ^ k))
            (Real.exp_pos _)
            conclusion_golden_radius_neutralization_multiplicative_recursion_phi
      _ =
          Real.rpow
            (conclusion_golden_radius_neutralization_multiplicative_recursion_r k)
            conclusion_golden_radius_neutralization_multiplicative_recursion_phi := by
        rw [conclusion_golden_radius_neutralization_multiplicative_recursion_r]

end Omega.Conclusion
