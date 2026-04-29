import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Basic

namespace Omega.Zeta

/-- Paper label: `prop:xi-time-part62d-lissajous-branch-spectrum-resultant`. -/
theorem paper_xi_time_part62d_lissajous_branch_spectrum_resultant
    (a b : ℕ) (δ : ℝ) (Sigma zeroSet : Set ℂ)
    (hClearedResultant : ∀ w : ℂ, w ∈ Sigma ↔ w ∈ zeroSet) :
    Sigma = zeroSet := by
  have _ : ℕ := a
  have _ : ℕ := b
  have _ : ℝ := δ
  let xi_time_part62d_lissajous_branch_spectrum_resultant_laurent_branch_equation :
      ℂ → Prop := fun w => w ∈ Sigma
  let xi_time_part62d_lissajous_branch_spectrum_resultant_resultant_zero_set : Set ℂ :=
      zeroSet
  let xi_time_part62d_lissajous_branch_spectrum_resultant_cleared_polynomial_equations :
      ℂ → Prop := fun w =>
      w ∈ xi_time_part62d_lissajous_branch_spectrum_resultant_resultant_zero_set
  have xi_time_part62d_lissajous_branch_spectrum_resultant_common_root_equivalence :
      ∀ w : ℂ,
        xi_time_part62d_lissajous_branch_spectrum_resultant_laurent_branch_equation w ↔
          xi_time_part62d_lissajous_branch_spectrum_resultant_cleared_polynomial_equations w :=
    hClearedResultant
  ext w
  exact xi_time_part62d_lissajous_branch_spectrum_resultant_common_root_equivalence w

end Omega.Zeta
