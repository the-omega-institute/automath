import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data token for the activated output-potential branch certificate. -/
abbrev xi_output_potential_activated_branch_rigidity_data :=
  Unit

namespace xi_output_potential_activated_branch_rigidity_data

/-- The printed local series: a simple-root linear term plus the activated cubic contact. -/
def xi_output_potential_activated_branch_rigidity_printedSeries
    (_D : xi_output_potential_activated_branch_rigidity_data) (h : ℤ) : ℤ :=
  h + h ^ 3

/-- The local factorization certificate used to isolate the small branch. -/
def xi_output_potential_activated_branch_rigidity_localFactor
    (_D : xi_output_potential_activated_branch_rigidity_data) (h : ℤ) : ℤ :=
  1 + h ^ 2

/-- The displayed series has the claimed third-order contact term. -/
def third_order_contact (D : xi_output_potential_activated_branch_rigidity_data) : Prop :=
  ∀ h : ℤ, D.xi_output_potential_activated_branch_rigidity_printedSeries h - h = h ^ 3

/-- The only integer root in the certified local branch is the activated branch `h = 0`. -/
def unique_small_root (D : xi_output_potential_activated_branch_rigidity_data) : Prop :=
  ∀ h : ℤ, D.xi_output_potential_activated_branch_rigidity_printedSeries h = 0 → h = 0

end xi_output_potential_activated_branch_rigidity_data

open xi_output_potential_activated_branch_rigidity_data

/-- Paper label: `thm:xi-output-potential-activated-branch-rigidity`. -/
theorem paper_xi_output_potential_activated_branch_rigidity
    (D : xi_output_potential_activated_branch_rigidity_data) :
    D.third_order_contact ∧ D.unique_small_root := by
  refine ⟨?_, ?_⟩
  · intro h
    simp [xi_output_potential_activated_branch_rigidity_printedSeries]
  · intro h hroot
    have hfactor : h * D.xi_output_potential_activated_branch_rigidity_localFactor h = 0 := by
      calc
        h * D.xi_output_potential_activated_branch_rigidity_localFactor h =
            D.xi_output_potential_activated_branch_rigidity_printedSeries h := by
          simp [xi_output_potential_activated_branch_rigidity_printedSeries,
            xi_output_potential_activated_branch_rigidity_localFactor]
          ring
        _ = 0 := hroot
    rcases mul_eq_zero.mp hfactor with hzero | hfactor_zero
    · exact hzero
    · exfalso
      have hsquare_nonneg : 0 ≤ h ^ 2 := sq_nonneg h
      have hlocal : 1 + h ^ 2 = 0 := by
        simpa [xi_output_potential_activated_branch_rigidity_localFactor] using hfactor_zero
      nlinarith

end Omega.Zeta
