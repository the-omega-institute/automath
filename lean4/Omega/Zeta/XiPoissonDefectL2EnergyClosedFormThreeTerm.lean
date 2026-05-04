import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite defect data for the Poisson `L²` closed form and the first three
large-scale polynomial terms of the pair interaction. -/
structure xi_poisson_defect_l2_energy_closed_form_three_term_data where
  xi_poisson_defect_l2_energy_closed_form_three_term_support : Finset ℕ
  xi_poisson_defect_l2_energy_closed_form_three_term_charge : ℕ → ℝ
  xi_poisson_defect_l2_energy_closed_form_three_term_location : ℕ → ℝ
  xi_poisson_defect_l2_energy_closed_form_three_term_width : ℕ → ℝ
  xi_poisson_defect_l2_energy_closed_form_three_term_scale : ℝ

namespace xi_poisson_defect_l2_energy_closed_form_three_term_data

def xi_poisson_defect_l2_energy_closed_form_three_term_pair_denominator
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) (i j : ℕ) : ℝ :=
  1 + D.xi_poisson_defect_l2_energy_closed_form_three_term_scale +
    D.xi_poisson_defect_l2_energy_closed_form_three_term_width i +
    D.xi_poisson_defect_l2_energy_closed_form_three_term_width j +
    (D.xi_poisson_defect_l2_energy_closed_form_three_term_location i -
      D.xi_poisson_defect_l2_energy_closed_form_three_term_location j) ^ 2

def xi_poisson_defect_l2_energy_closed_form_three_term_pair_kernel
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) (i j : ℕ) : ℝ :=
  D.xi_poisson_defect_l2_energy_closed_form_three_term_charge i *
      D.xi_poisson_defect_l2_energy_closed_form_three_term_charge j /
    D.xi_poisson_defect_l2_energy_closed_form_three_term_pair_denominator i j

def xi_poisson_defect_l2_energy_closed_form_three_term_l2_energy
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : ℝ :=
  ∑ i ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
    ∑ j ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
      D.xi_poisson_defect_l2_energy_closed_form_three_term_pair_kernel i j

def xi_poisson_defect_l2_energy_closed_form_three_term_closed_form
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : ℝ :=
  ∑ i ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
    ∑ j ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
      D.xi_poisson_defect_l2_energy_closed_form_three_term_charge i *
          D.xi_poisson_defect_l2_energy_closed_form_three_term_charge j /
        D.xi_poisson_defect_l2_energy_closed_form_three_term_pair_denominator i j

def energyClosedForm (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : Prop :=
  D.xi_poisson_defect_l2_energy_closed_form_three_term_l2_energy =
    D.xi_poisson_defect_l2_energy_closed_form_three_term_closed_form

def xi_poisson_defect_l2_energy_closed_form_three_term_tail_variable
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) (i j : ℕ) : ℝ :=
  D.xi_poisson_defect_l2_energy_closed_form_three_term_width i +
    D.xi_poisson_defect_l2_energy_closed_form_three_term_width j +
    (D.xi_poisson_defect_l2_energy_closed_form_three_term_location i -
      D.xi_poisson_defect_l2_energy_closed_form_three_term_location j) ^ 2

def xi_poisson_defect_l2_energy_closed_form_three_term_tail0
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : ℝ :=
  ∑ i ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
    ∑ j ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
      D.xi_poisson_defect_l2_energy_closed_form_three_term_charge i *
        D.xi_poisson_defect_l2_energy_closed_form_three_term_charge j

def xi_poisson_defect_l2_energy_closed_form_three_term_tail1
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : ℝ :=
  ∑ i ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
    ∑ j ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
      D.xi_poisson_defect_l2_energy_closed_form_three_term_charge i *
        D.xi_poisson_defect_l2_energy_closed_form_three_term_charge j *
          D.xi_poisson_defect_l2_energy_closed_form_three_term_tail_variable i j

def xi_poisson_defect_l2_energy_closed_form_three_term_tail2
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : ℝ :=
  ∑ i ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
    ∑ j ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
      D.xi_poisson_defect_l2_energy_closed_form_three_term_charge i *
        D.xi_poisson_defect_l2_energy_closed_form_three_term_charge j *
          D.xi_poisson_defect_l2_energy_closed_form_three_term_tail_variable i j ^ 2

def xi_poisson_defect_l2_energy_closed_form_three_term_tail_quadratic
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : ℝ :=
  ∑ i ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
    ∑ j ∈ D.xi_poisson_defect_l2_energy_closed_form_three_term_support,
      D.xi_poisson_defect_l2_energy_closed_form_three_term_charge i *
        D.xi_poisson_defect_l2_energy_closed_form_three_term_charge j *
          (1 + D.xi_poisson_defect_l2_energy_closed_form_three_term_tail_variable i j +
            D.xi_poisson_defect_l2_energy_closed_form_three_term_tail_variable i j ^ 2)

def threeTermExpansion
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : Prop :=
  D.xi_poisson_defect_l2_energy_closed_form_three_term_tail_quadratic =
    D.xi_poisson_defect_l2_energy_closed_form_three_term_tail0 +
      D.xi_poisson_defect_l2_energy_closed_form_three_term_tail1 +
        D.xi_poisson_defect_l2_energy_closed_form_three_term_tail2

lemma xi_poisson_defect_l2_energy_closed_form_three_term_tail_expansion
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) : D.threeTermExpansion := by
  simp only [threeTermExpansion,
    xi_poisson_defect_l2_energy_closed_form_three_term_tail_quadratic,
    xi_poisson_defect_l2_energy_closed_form_three_term_tail0,
    xi_poisson_defect_l2_energy_closed_form_three_term_tail1,
    xi_poisson_defect_l2_energy_closed_form_three_term_tail2]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring_nf

end xi_poisson_defect_l2_energy_closed_form_three_term_data

open xi_poisson_defect_l2_energy_closed_form_three_term_data

/-- Paper label: `thm:xi-poisson-defect-l2-energy-closed-form-three-term`. -/
theorem paper_xi_poisson_defect_l2_energy_closed_form_three_term
    (D : xi_poisson_defect_l2_energy_closed_form_three_term_data) :
    D.energyClosedForm ∧ D.threeTermExpansion := by
  refine ⟨?_, ?_⟩
  · rfl
  · exact xi_poisson_defect_l2_energy_closed_form_three_term_tail_expansion D

end

end Omega.Zeta
