import Mathlib.Tactic
import Omega.POM.MultiplicityLambdaqLargeQAsymptotic
import Omega.POM.MultiplicityLambdaqTaylorQ0

namespace Omega.POM

noncomputable section

/-- The first Gibbs mass in the two-block real-`q` multiplicity pressure model. -/
def pom_multiplicity_lambdaq_derivative_gibbs_p1 (q : ℝ) : ℝ :=
  pomRealQWeight q * pomRealQRoot q

/-- The second Gibbs mass in the two-block real-`q` multiplicity pressure model. -/
def pom_multiplicity_lambdaq_derivative_gibbs_p2 (q : ℝ) : ℝ :=
  pomRealQWeight q * pomRealQRoot q ^ (2 : Nat)

/-- Gibbs numerator for the logarithmic `q`-derivative. -/
def pom_multiplicity_lambdaq_derivative_gibbs_numerator (q : ℝ) : ℝ :=
  pom_multiplicity_lambdaq_derivative_gibbs_p1 q / pomRealQWeight q +
    pom_multiplicity_lambdaq_derivative_gibbs_p2 q / pomRealQWeight q

/-- Gibbs denominator, the expected block length. -/
def pom_multiplicity_lambdaq_derivative_gibbs_denominator (q : ℝ) : ℝ :=
  pom_multiplicity_lambdaq_derivative_gibbs_p1 q +
    2 * pom_multiplicity_lambdaq_derivative_gibbs_p2 q

/-- The Gibbs-ratio expression for `d/dq log λ(q)` in the two-block surrogate. -/
def pom_multiplicity_lambdaq_derivative_gibbs_ratio (q : ℝ) : ℝ :=
  pom_multiplicity_lambdaq_derivative_gibbs_numerator q /
    pom_multiplicity_lambdaq_derivative_gibbs_denominator q

/-- Closed form of the same logarithmic derivative after using `W_q(ρ(q)) = 1`. -/
def pom_multiplicity_lambdaq_derivative_gibbs_closed (q : ℝ) : ℝ :=
  (1 + pomRealQRoot q) / (pomRealQWeight q * (1 + 2 * pomRealQRoot q))

/-- Paper label: `prop:pom-multiplicity-lambdaq-derivative-gibbs`.
For the concrete real-`q` multiplicity pressure model, the two Gibbs masses normalize to one;
the implicit derivative ratio is therefore the Gibbs numerator divided by the expected block
length, and the same ratio reduces to the displayed closed form. The endpoint packages are the
existing Taylor-at-zero and large-`q` wrappers. -/
theorem paper_pom_multiplicity_lambdaq_derivative_gibbs (q : ℝ) (hq : 0 < q) :
    pom_multiplicity_lambdaq_derivative_gibbs_p1 q +
        pom_multiplicity_lambdaq_derivative_gibbs_p2 q = 1 ∧
      pom_multiplicity_lambdaq_derivative_gibbs_numerator q = (pomRealQWeight q)⁻¹ ∧
      pom_multiplicity_lambdaq_derivative_gibbs_denominator q =
        pomRealQWeight q * pomRealQRoot q * (1 + 2 * pomRealQRoot q) ∧
      pom_multiplicity_lambdaq_derivative_gibbs_ratio q =
        pom_multiplicity_lambdaq_derivative_gibbs_closed q ∧
      pom_multiplicity_lambdaq_large_q_asymptotic_statement ∧
      (∀ D : pom_multiplicity_lambdaq_taylor_q0_data, D.hasSecondOrderExpansion) := by
  have hpressure := paper_pom_multiplicity_real_q_pressure
  have hroot_series : pomRealQSeries q (pomRealQRoot q) = 1 :=
    (hpressure.1 q hq).2.2.1
  have hw_pos : 0 < pomRealQWeight q := by
    unfold pomRealQWeight
    linarith
  have hw_ne : pomRealQWeight q ≠ 0 := ne_of_gt hw_pos
  have hr_pos : 0 < pomRealQRoot q := (hpressure.1 q hq).1
  have hr_ne : pomRealQRoot q ≠ 0 := ne_of_gt hr_pos
  have hsum :
      pom_multiplicity_lambdaq_derivative_gibbs_p1 q +
          pom_multiplicity_lambdaq_derivative_gibbs_p2 q = 1 := by
    simpa [pomRealQSeries, pom_multiplicity_lambdaq_derivative_gibbs_p1,
      pom_multiplicity_lambdaq_derivative_gibbs_p2, mul_add] using hroot_series
  have hroot_mul :
      pomRealQWeight q * pomRealQRoot q * (1 + pomRealQRoot q) = 1 := by
    unfold pomRealQSeries at hroot_series
    nlinarith [hroot_series]
  have hnum :
      pom_multiplicity_lambdaq_derivative_gibbs_numerator q = (pomRealQWeight q)⁻¹ := by
    calc
      pom_multiplicity_lambdaq_derivative_gibbs_numerator q
          = (pom_multiplicity_lambdaq_derivative_gibbs_p1 q +
              pom_multiplicity_lambdaq_derivative_gibbs_p2 q) / pomRealQWeight q := by
              rw [pom_multiplicity_lambdaq_derivative_gibbs_numerator]
              ring
      _ = 1 / pomRealQWeight q := by rw [hsum]
      _ = (pomRealQWeight q)⁻¹ := by rw [one_div]
  have hden :
      pom_multiplicity_lambdaq_derivative_gibbs_denominator q =
        pomRealQWeight q * pomRealQRoot q * (1 + 2 * pomRealQRoot q) := by
    rw [pom_multiplicity_lambdaq_derivative_gibbs_denominator,
      pom_multiplicity_lambdaq_derivative_gibbs_p1,
      pom_multiplicity_lambdaq_derivative_gibbs_p2]
    ring
  have hfactor_pos : 0 < 1 + 2 * pomRealQRoot q := by positivity
  have hratio :
      pom_multiplicity_lambdaq_derivative_gibbs_ratio q =
        pom_multiplicity_lambdaq_derivative_gibbs_closed q := by
    rw [pom_multiplicity_lambdaq_derivative_gibbs_ratio,
      pom_multiplicity_lambdaq_derivative_gibbs_closed, hnum, hden]
    field_simp [hw_ne, hr_ne, ne_of_gt hfactor_pos]
    nlinarith [hroot_mul]
  exact ⟨hsum, hnum, hden, hratio, paper_pom_multiplicity_lambdaq_large_q_asymptotic,
    fun D => paper_pom_multiplicity_lambdaq_taylor_q0 D⟩

end

end Omega.POM
