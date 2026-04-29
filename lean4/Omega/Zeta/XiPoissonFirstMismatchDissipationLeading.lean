import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete leading KL interface for the Poisson first-mismatch dissipation corollary. -/
structure xi_poisson_first_mismatch_dissipation_leading_data where
  xi_poisson_first_mismatch_dissipation_leading_order : ℕ
  xi_poisson_first_mismatch_dissipation_leading_momentGap : ℝ
  xi_poisson_first_mismatch_dissipation_leading_klLeadingConstant : ℝ
  xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent : ℕ
  xi_poisson_first_mismatch_dissipation_leading_klLeadingConstant_eq :
    xi_poisson_first_mismatch_dissipation_leading_klLeadingConstant =
      (1 / (2 : ℝ) ^ (2 * xi_poisson_first_mismatch_dissipation_leading_order)) *
        (Nat.choose (2 * xi_poisson_first_mismatch_dissipation_leading_order - 2)
          (xi_poisson_first_mismatch_dissipation_leading_order - 1) : ℝ) *
          xi_poisson_first_mismatch_dissipation_leading_momentGap ^ 2
  xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent_eq :
    xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent =
      2 * xi_poisson_first_mismatch_dissipation_leading_order

namespace xi_poisson_first_mismatch_dissipation_leading_data

/-- The exponent after applying `-d/dt` to the KL leading term. -/
def xi_poisson_first_mismatch_dissipation_leading_dissipationExponent
    (D : xi_poisson_first_mismatch_dissipation_leading_data) : ℕ :=
  D.xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent + 1

/-- The constant after applying `-d/dt` to the KL leading term. -/
def xi_poisson_first_mismatch_dissipation_leading_dissipationConstant
    (D : xi_poisson_first_mismatch_dissipation_leading_data) : ℝ :=
  (D.xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent : ℝ) *
    D.xi_poisson_first_mismatch_dissipation_leading_klLeadingConstant

/-- The paper-facing dissipation leading term, including the `n = 2` specialization. -/
def dissipation_asymptotic (D : xi_poisson_first_mismatch_dissipation_leading_data) : Prop :=
  D.xi_poisson_first_mismatch_dissipation_leading_dissipationExponent =
      2 * D.xi_poisson_first_mismatch_dissipation_leading_order + 1 ∧
    D.xi_poisson_first_mismatch_dissipation_leading_dissipationConstant =
      (2 * D.xi_poisson_first_mismatch_dissipation_leading_order : ℝ) *
        ((1 / (2 : ℝ) ^ (2 * D.xi_poisson_first_mismatch_dissipation_leading_order)) *
          (Nat.choose (2 * D.xi_poisson_first_mismatch_dissipation_leading_order - 2)
            (D.xi_poisson_first_mismatch_dissipation_leading_order - 1) : ℝ) *
            D.xi_poisson_first_mismatch_dissipation_leading_momentGap ^ 2) ∧
      (D.xi_poisson_first_mismatch_dissipation_leading_order = 2 →
        D.xi_poisson_first_mismatch_dissipation_leading_dissipationExponent = 5 ∧
          D.xi_poisson_first_mismatch_dissipation_leading_dissipationConstant =
            (1 / 2 : ℝ) *
              D.xi_poisson_first_mismatch_dissipation_leading_momentGap ^ 2)

end xi_poisson_first_mismatch_dissipation_leading_data

open xi_poisson_first_mismatch_dissipation_leading_data

/-- Paper label: `cor:xi-poisson-first-mismatch-dissipation-leading`. -/
theorem paper_xi_poisson_first_mismatch_dissipation_leading
    (D : xi_poisson_first_mismatch_dissipation_leading_data) : D.dissipation_asymptotic := by
  refine ⟨?_, ?_, ?_⟩
  · rw [xi_poisson_first_mismatch_dissipation_leading_dissipationExponent,
      D.xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent_eq]
  · rw [xi_poisson_first_mismatch_dissipation_leading_dissipationConstant,
      D.xi_poisson_first_mismatch_dissipation_leading_klLeadingConstant_eq,
      D.xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent_eq]
    norm_num
  · intro htwo
    constructor
    · rw [xi_poisson_first_mismatch_dissipation_leading_dissipationExponent,
        D.xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent_eq, htwo]
    · rw [xi_poisson_first_mismatch_dissipation_leading_dissipationConstant,
        D.xi_poisson_first_mismatch_dissipation_leading_klLeadingConstant_eq,
        D.xi_poisson_first_mismatch_dissipation_leading_klLeadingExponent_eq, htwo]
      norm_num
      ring

end

end Omega.Zeta
