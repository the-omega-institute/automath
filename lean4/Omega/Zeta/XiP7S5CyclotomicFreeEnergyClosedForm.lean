import Mathlib.Tactic

namespace Omega.Zeta

/-- The finite atomic orbit sum used by the cyclotomic free-energy closed form. -/
noncomputable def xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum
    (n : ℕ) (u : ℝ) : ℝ :=
  (Finset.range n).sum fun k => u ^ k

/-- The real third cyclotomic factor, written as an explicit polynomial. -/
noncomputable def xi_p7_s5_cyclotomic_free_energy_closed_form_phi3 (u : ℝ) : ℝ :=
  1 + u + u ^ 2

/-- The real fifth cyclotomic factor, written as an explicit polynomial. -/
noncomputable def xi_p7_s5_cyclotomic_free_energy_closed_form_phi5 (u : ℝ) : ℝ :=
  1 + u + u ^ 2 + u ^ 3 + u ^ 4

/-- The real seventh cyclotomic factor, written as an explicit polynomial. -/
noncomputable def xi_p7_s5_cyclotomic_free_energy_closed_form_phi7 (u : ℝ) : ℝ :=
  1 + u + u ^ 2 + u ^ 3 + u ^ 4 + u ^ 5 + u ^ 6

/-- Concrete closed-form package for the three finite orbit sums and the denominator-cleared
single-valuedness identity at the seventh cyclotomic factor. -/
def xi_p7_s5_cyclotomic_free_energy_closed_form_statement (u : ℝ) : Prop :=
  xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum 3 u =
      xi_p7_s5_cyclotomic_free_energy_closed_form_phi3 u ∧
    xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum 5 u =
      xi_p7_s5_cyclotomic_free_energy_closed_form_phi5 u ∧
    xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum 7 u =
      xi_p7_s5_cyclotomic_free_energy_closed_form_phi7 u ∧
    (u - 1) * xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum 7 u = u ^ 7 - 1

/-- Paper label: `thm:xi-p7-s5-cyclotomic-free-energy-closed-form`. -/
theorem paper_xi_p7_s5_cyclotomic_free_energy_closed_form
    (u : ℝ) (_hu0 : 0 < u) (_hu1 : u ≠ 1) :
    xi_p7_s5_cyclotomic_free_energy_closed_form_statement u := by
  repeat' constructor
  · simp [xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum,
      xi_p7_s5_cyclotomic_free_energy_closed_form_phi3, Finset.sum_range_succ]
  · simp [xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum,
      xi_p7_s5_cyclotomic_free_energy_closed_form_phi5, Finset.sum_range_succ]
  · simp [xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum,
      xi_p7_s5_cyclotomic_free_energy_closed_form_phi7, Finset.sum_range_succ]
  · simp [xi_p7_s5_cyclotomic_free_energy_closed_form_orbitSum, Finset.sum_range_succ]
    ring_nf

end Omega.Zeta
