import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The Perron root of the untwisted probe. -/
def conclusion_prime_root_unity_probe_quadratic_resolution_lambda : ℝ :=
  1

/-- The quadratic Taylor coefficient of the local root-unity shadow. -/
def conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff : ℝ :=
  (6 * Real.sqrt 5 - 5) / 250

/-- The quartic Taylor coefficient of the local root-unity shadow. -/
def conclusion_prime_root_unity_probe_quadratic_resolution_quarticCoeff : ℝ :=
  (7 + 24 * Real.sqrt 5) / 75000

/-- The local real-analytic shadow `ρ(t)` used by the quadratic-resolution wrapper. -/
def conclusion_prime_root_unity_probe_quadratic_resolution_rho (t : ℝ) : ℝ :=
  Real.exp
    (-conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff * t ^ 2 +
      conclusion_prime_root_unity_probe_quadratic_resolution_quarticCoeff * t ^ 4)

/-- The least nontrivial root-of-unity angle at prime modulus `p`. -/
def conclusion_prime_root_unity_probe_quadratic_resolution_tp (p : ℕ) : ℝ :=
  2 * Real.pi / p

private lemma conclusion_prime_root_unity_probe_quadratic_resolution_log_formula (t : ℝ) :
    Real.log
        (conclusion_prime_root_unity_probe_quadratic_resolution_rho t /
          conclusion_prime_root_unity_probe_quadratic_resolution_lambda) =
      -conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff * t ^ 2 +
        conclusion_prime_root_unity_probe_quadratic_resolution_quarticCoeff * t ^ 4 := by
  rw [conclusion_prime_root_unity_probe_quadratic_resolution_rho,
    conclusion_prime_root_unity_probe_quadratic_resolution_lambda, div_one, Real.log_exp]

private lemma conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff_pos :
    0 < conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff := by
  unfold conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff
  have hsqrt_gt_one : (1 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  nlinarith

/-- Concrete paper-facing package for the prime root-unity probe: the logarithmic distortion has
an explicit quadratic-plus-quartic expansion, the same closed form survives after substituting
`t = 2π / p`, and the leading quadratic coefficient is strictly positive. -/
def conclusion_prime_root_unity_probe_quadratic_resolution_statement : Prop :=
  (∀ t : ℝ,
      Real.log
          (conclusion_prime_root_unity_probe_quadratic_resolution_rho t /
            conclusion_prime_root_unity_probe_quadratic_resolution_lambda) =
        -conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff * t ^ 2 +
          conclusion_prime_root_unity_probe_quadratic_resolution_quarticCoeff * t ^ 4) ∧
    (∀ p : ℕ, Nat.Prime p → p ≠ 2 →
      Real.log
          (conclusion_prime_root_unity_probe_quadratic_resolution_rho
              (conclusion_prime_root_unity_probe_quadratic_resolution_tp p) /
            conclusion_prime_root_unity_probe_quadratic_resolution_lambda) =
        -conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff *
            (conclusion_prime_root_unity_probe_quadratic_resolution_tp p) ^ 2 +
          conclusion_prime_root_unity_probe_quadratic_resolution_quarticCoeff *
            (conclusion_prime_root_unity_probe_quadratic_resolution_tp p) ^ 4) ∧
    0 < conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff

/-- Paper label: `prop:conclusion-prime-root-unity-probe-quadratic-resolution`. -/
theorem paper_conclusion_prime_root_unity_probe_quadratic_resolution :
    conclusion_prime_root_unity_probe_quadratic_resolution_statement := by
  refine ⟨conclusion_prime_root_unity_probe_quadratic_resolution_log_formula, ?_,
    conclusion_prime_root_unity_probe_quadratic_resolution_quadraticCoeff_pos⟩
  intro p _hp _hodd
  exact conclusion_prime_root_unity_probe_quadratic_resolution_log_formula
    (conclusion_prime_root_unity_probe_quadratic_resolution_tp p)

end

end Omega.Conclusion
