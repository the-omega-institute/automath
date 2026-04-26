import Mathlib.Tactic
import Omega.Zeta.XiPoissonKlSixthOrderMu3Mu4

namespace Omega.Conclusion

noncomputable section

/-- Concrete coefficient data for the Poisson--Cauchy skewness wrapper. -/
structure conclusion_poisson_skewness_first_enters_at_sextic_Data where
  conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq : ℝ
  conclusion_poisson_skewness_first_enters_at_sextic_m3 : ℝ
  conclusion_poisson_skewness_first_enters_at_sextic_m4 : ℝ

/-- Convert the conclusion-level moments into the existing Poisson--Cauchy KL coefficient data. -/
def conclusion_poisson_skewness_first_enters_at_sextic_coefficient_data
    (sigmaSq m3 m4 : ℝ) :
    Omega.Zeta.xi_poisson_cauchy_kl_two_term_explicit_coeff_data where
  xi_poisson_cauchy_kl_two_term_explicit_coeff_sigma_sq := sigmaSq
  xi_poisson_cauchy_kl_two_term_explicit_coeff_m3 := m3
  xi_poisson_cauchy_kl_two_term_explicit_coeff_m4 := m4

namespace conclusion_poisson_skewness_first_enters_at_sextic_Data

/-- The quartic coefficient is independent of the skewness moment. -/
def quarticBlind (D : conclusion_poisson_skewness_first_enters_at_sextic_Data) : Prop :=
  ∀ m3' : ℝ,
    (conclusion_poisson_skewness_first_enters_at_sextic_coefficient_data
        D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq m3'
        D.conclusion_poisson_skewness_first_enters_at_sextic_m4).xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t4_coeff =
      (conclusion_poisson_skewness_first_enters_at_sextic_coefficient_data
        D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq
        D.conclusion_poisson_skewness_first_enters_at_sextic_m3
        D.conclusion_poisson_skewness_first_enters_at_sextic_m4).xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t4_coeff

/-- The sextic coefficient carries the first explicit skewness square. -/
def sexticSkewnessFingerprint
    (D : conclusion_poisson_skewness_first_enters_at_sextic_Data) : Prop :=
  (conclusion_poisson_skewness_first_enters_at_sextic_coefficient_data
      D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq
      D.conclusion_poisson_skewness_first_enters_at_sextic_m3
      D.conclusion_poisson_skewness_first_enters_at_sextic_m4).xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t6_coeff =
    D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq ^ 3 / 64 -
      D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq *
          D.conclusion_poisson_skewness_first_enters_at_sextic_m4 /
        8 +
        3 * D.conclusion_poisson_skewness_first_enters_at_sextic_m3 ^ 2 / 32

/-- With zero skewness, the sextic skewness contribution vanishes. -/
def symmetricImpliesEighthOrder
    (D : conclusion_poisson_skewness_first_enters_at_sextic_Data) : Prop :=
  D.conclusion_poisson_skewness_first_enters_at_sextic_m3 = 0 →
    (conclusion_poisson_skewness_first_enters_at_sextic_coefficient_data
        D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq
        D.conclusion_poisson_skewness_first_enters_at_sextic_m3
        D.conclusion_poisson_skewness_first_enters_at_sextic_m4).xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t6_coeff =
      D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq ^ 3 / 64 -
        D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq *
            D.conclusion_poisson_skewness_first_enters_at_sextic_m4 /
          8

end conclusion_poisson_skewness_first_enters_at_sextic_Data

/-- Paper label: `cor:conclusion-poisson-skewness-first-enters-at-sextic`. -/
theorem paper_conclusion_poisson_skewness_first_enters_at_sextic
    (D : conclusion_poisson_skewness_first_enters_at_sextic_Data) :
    D.quarticBlind ∧ D.sexticSkewnessFingerprint ∧ D.symmetricImpliesEighthOrder := by
  refine ⟨?_, ?_, ?_⟩
  · intro m3'
    rfl
  · exact Omega.Zeta.paper_xi_poisson_kl_sixth_order_mu3_mu4
      (conclusion_poisson_skewness_first_enters_at_sextic_coefficient_data
        D.conclusion_poisson_skewness_first_enters_at_sextic_sigma_sq
        D.conclusion_poisson_skewness_first_enters_at_sextic_m3
        D.conclusion_poisson_skewness_first_enters_at_sextic_m4)
  · intro hm3
    dsimp [conclusion_poisson_skewness_first_enters_at_sextic_coefficient_data,
      Omega.Zeta.xi_poisson_cauchy_kl_two_term_explicit_coeff_data.xi_poisson_cauchy_kl_two_term_explicit_coeff_kl_t6_coeff]
    rw [hm3]
    ring

end

end Omega.Conclusion
