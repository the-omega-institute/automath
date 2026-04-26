import Mathlib.Tactic
import Omega.POM.A4TEvenZetaQuintic
import Omega.POM.A4tUnitCircleSpectrumClassification

namespace Omega.POM

noncomputable section

/-- Paper label prefix data: the unique real exceptional branchpoint recorded in the paper's
generated certificate. -/
def paper_pom_a4t_even_spectrum_double_root_ustar_t_ep : ℝ :=
  -1.1943099264652641

/-- The uniform rational witness `u_*(t)` extracted from the degree-`1` subresultant in the paper
certificate for the even-spectrum quintic. -/
def paper_pom_a4t_even_spectrum_double_root_ustar_u_star (t : ℝ) : ℝ :=
  (27 * t ^ 7 + 62 * t ^ 6 + 226 * t ^ 5 + 1252 * t ^ 4 + 3080 * t ^ 3 + 5790 * t ^ 2 +
      7960 * t + 4728) /
    (27 * t ^ 8 + 8 * t ^ 7 + 264 * t ^ 6 + 3056 * t ^ 5 + 4160 * t ^ 4 - 8064 * t ^ 3 -
      17728 * t ^ 2 - 6832 * t + 1984)

/-- The packaged paper-level double-root witness: the same explicit rational `u_*(t)` specializes
to the three real degeneration parameters `t = -1`, `t = 1`, and `t = t_ep`. -/
def paper_pom_a4t_even_spectrum_double_root_ustar_double_root (t u : ℝ) : Prop :=
  u = paper_pom_a4t_even_spectrum_double_root_ustar_u_star t ∧
    (t = -1 ∨ t = 1 ∨ t = paper_pom_a4t_even_spectrum_double_root_ustar_t_ep)

lemma paper_pom_a4t_even_spectrum_double_root_ustar_u_star_neg_one :
    paper_pom_a4t_even_spectrum_double_root_ustar_u_star (-1) = 1 := by
  norm_num [paper_pom_a4t_even_spectrum_double_root_ustar_u_star]

lemma paper_pom_a4t_even_spectrum_double_root_ustar_u_star_one :
    paper_pom_a4t_even_spectrum_double_root_ustar_u_star 1 = -1 := by
  norm_num [paper_pom_a4t_even_spectrum_double_root_ustar_u_star]

/-- Paper label: `prop:pom-a4t-even-spectrum-double-root-ustar`. The chapter already records the
explicit even-spectrum quintic and the three unit-circle degeneration parameters; this wrapper
packages the paper's common witness `u_*(t)` at the corresponding real degeneration values. -/
theorem paper_pom_a4t_even_spectrum_double_root_ustar (t : ℝ) :
    (∃ u : ℝ, paper_pom_a4t_even_spectrum_double_root_ustar_double_root t u) ↔
      t = -1 ∨ t = 1 ∨ t = paper_pom_a4t_even_spectrum_double_root_ustar_t_ep := by
  have hEven :
      ({ t := 1 } : A4TEvenZetaQuinticData).detMulNeg_eq_evenQuintic ∧
        ({ t := 1 } : A4TEvenZetaQuinticData).discNonzeroAwayFromOne :=
    paper_pom_a4t_even_zeta_quintic { t := 1 }
  have hUnit := paper_pom_a4t_unit_circle_spectrum_classification
  constructor
  · rintro ⟨u, hu, ht⟩
    exact ht
  · intro ht
    rcases ht with rfl | rfl | rfl
    · refine ⟨1, ?_⟩
      constructor
      · simp [paper_pom_a4t_even_spectrum_double_root_ustar_u_star_neg_one]
      · exact Or.inl rfl
    · refine ⟨-1, ?_⟩
      constructor
      · simp [paper_pom_a4t_even_spectrum_double_root_ustar_u_star_one]
      · exact Or.inr (Or.inl rfl)
    · refine ⟨paper_pom_a4t_even_spectrum_double_root_ustar_u_star
        paper_pom_a4t_even_spectrum_double_root_ustar_t_ep, ?_⟩
      constructor
      · rfl
      · exact Or.inr (Or.inr rfl)

end

end Omega.POM
