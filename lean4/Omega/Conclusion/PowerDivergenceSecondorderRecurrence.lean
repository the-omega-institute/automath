import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete two-root data for the power-divergence spectrum. Positive coefficients and distinct
exponential rates force a genuine two-exponential model. -/
structure PowerDivergenceSpectrumData where
  leftWeight : ℝ
  rightWeight : ℝ
  leftRate : ℝ
  rightRate : ℝ
  hleftWeight : 0 < leftWeight
  hrightWeight : 0 < rightWeight
  hrate : leftRate < rightRate

namespace PowerDivergenceSpectrumData

/-- The two exponential roots of the characteristic polynomial. -/
noncomputable def leftRoot (D : PowerDivergenceSpectrumData) : ℝ :=
  Real.exp D.leftRate

/-- The two exponential roots of the characteristic polynomial. -/
noncomputable def rightRoot (D : PowerDivergenceSpectrumData) : ℝ :=
  Real.exp D.rightRate

/-- Closed-form spectrum modeled by a positive two-exponential sum. -/
noncomputable def spectrum (D : PowerDivergenceSpectrumData) (n : ℕ) : ℝ :=
  D.leftWeight * D.leftRoot ^ n + D.rightWeight * D.rightRoot ^ n

/-- The spectrum is given explicitly by the two exponentials with rates `leftRate` and
`rightRate`. -/
def explicitFormula (D : PowerDivergenceSpectrumData) : Prop :=
  ∀ n : ℕ,
    D.spectrum n =
      D.leftWeight * Real.exp (D.leftRate * n) +
        D.rightWeight * Real.exp (D.rightRate * n)

/-- Order-two recurrence associated to the roots `e^{leftRate}` and `e^{rightRate}`. -/
def secondOrderRecurrence (D : PowerDivergenceSpectrumData) : Prop :=
  ∀ n : ℕ,
    D.spectrum (n + 2) =
      (D.leftRoot + D.rightRoot) * D.spectrum (n + 1) -
        (D.leftRoot * D.rightRoot) * D.spectrum n

/-- Strict discrete log-convexity of the positive two-exponential spectrum. -/
def strictLogConvex (D : PowerDivergenceSpectrumData) : Prop :=
  ∀ n : ℕ, D.spectrum n * D.spectrum (n + 2) > D.spectrum (n + 1) ^ 2

end PowerDivergenceSpectrumData

private lemma leftRoot_pos (D : PowerDivergenceSpectrumData) : 0 < D.leftRoot := by
  exact Real.exp_pos _

private lemma rightRoot_pos (D : PowerDivergenceSpectrumData) : 0 < D.rightRoot := by
  exact Real.exp_pos _

private lemma roots_ne (D : PowerDivergenceSpectrumData) : D.leftRoot ≠ D.rightRoot := by
  intro hEq
  exact (ne_of_lt D.hrate) <| Real.exp_strictMono.injective hEq

/-- The two-exponential closed form immediately yields the characteristic recurrence, and the
mixed term factorization gives strict log-convexity.
    thm:conclusion-power-divergence-secondorder-recurrence -/
theorem paper_conclusion_power_divergence_secondorder_recurrence
    (D : PowerDivergenceSpectrumData) :
    D.explicitFormula ∧ D.secondOrderRecurrence ∧ D.strictLogConvex := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [PowerDivergenceSpectrumData.spectrum, PowerDivergenceSpectrumData.leftRoot,
      PowerDivergenceSpectrumData.rightRoot]
    rw [← Real.exp_nat_mul D.leftRate n, ← Real.exp_nat_mul D.rightRate n]
    simp [mul_comm]
  · intro n
    simp [PowerDivergenceSpectrumData.spectrum, PowerDivergenceSpectrumData.leftRoot,
      PowerDivergenceSpectrumData.rightRoot, pow_add, pow_one, pow_two, mul_add, add_mul,
      sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
    ring
  · intro n
    have hfactor :
        D.spectrum n * D.spectrum (n + 2) - D.spectrum (n + 1) ^ 2 =
          D.leftWeight * D.rightWeight * (D.leftRoot ^ n) * (D.rightRoot ^ n) *
            (D.leftRoot - D.rightRoot) ^ 2 := by
      simp [PowerDivergenceSpectrumData.spectrum, PowerDivergenceSpectrumData.leftRoot,
        PowerDivergenceSpectrumData.rightRoot, pow_add, pow_one, pow_two, mul_add,
        sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      ring
    have hsq : 0 < (D.leftRoot - D.rightRoot) ^ 2 := by
      exact sq_pos_iff.mpr (sub_ne_zero.mpr (roots_ne D))
    have hcoeff : 0 < D.leftWeight * D.rightWeight := mul_pos D.hleftWeight D.hrightWeight
    have hroots : 0 < D.leftRoot ^ n * D.rightRoot ^ n := by
      exact mul_pos (pow_pos (leftRoot_pos D) _) (pow_pos (rightRoot_pos D) _)
    have hpos :
        0 <
          D.leftWeight * D.rightWeight * (D.leftRoot ^ n) * (D.rightRoot ^ n) *
            (D.leftRoot - D.rightRoot) ^ 2 := by
      have hmain : 0 < D.leftWeight * D.rightWeight * (D.leftRoot ^ n) * D.rightRoot ^ n := by
        simpa [mul_assoc] using mul_pos hcoeff hroots
      exact mul_pos hmain hsq
    have hdiff :
        0 < D.spectrum n * D.spectrum (n + 2) - D.spectrum (n + 1) ^ 2 := by
      simpa [hfactor] using hpos
    nlinarith

end

end Omega.Conclusion
