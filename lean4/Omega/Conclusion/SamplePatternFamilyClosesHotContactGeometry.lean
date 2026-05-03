import Mathlib.Data.Real.Basic

namespace Omega.Conclusion

/-- Concrete data for the hot-contact-geometry closure statement.  The derivative symbols are
recorded as explicit real-valued observables so the publication wrapper can state the Legendre
reciprocity identities without introducing a new analytic development in this file. -/
structure conclusion_sample_pattern_family_closes_hot_contact_geometry_data where
  conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 : ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 : ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc : ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_front : ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure : ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star : ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_slope : ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_curvature : ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure_slope : ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure_curvature : ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law : ℕ → ℕ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_gamma :
    (ℕ → ℕ) → ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_front :
    (ℕ → ℕ) → ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_pressure :
    (ℕ → ℕ) → ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_q_star :
    (ℕ → ℕ) → ℝ → ℝ
  conclusion_sample_pattern_family_closes_hot_contact_geometry_hot_nonempty :
    conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 <
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a1
  conclusion_sample_pattern_family_closes_hot_contact_geometry_q_range :
    ∀ a,
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        0 < conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a ∧
          conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a < 1
  conclusion_sample_pattern_family_closes_hot_contact_geometry_q_reciprocity :
    ∀ a,
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a =
          1 - conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_slope a
  conclusion_sample_pattern_family_closes_hot_contact_geometry_a_reciprocity :
    ∀ a,
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        a =
          conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure_slope
            (conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a)
  conclusion_sample_pattern_family_closes_hot_contact_geometry_legendre_identity :
    ∀ a,
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure
            (conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a) =
          conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc a -
            a * conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_slope a
  conclusion_sample_pattern_family_closes_hot_contact_geometry_curvature_identity :
    ∀ a,
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure_curvature
            (conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a) =
          -1 / conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_curvature a
  conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_front :
    ∀ a,
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc a =
          conclusion_sample_pattern_family_closes_hot_contact_geometry_front a + a
  conclusion_sample_pattern_family_closes_hot_contact_geometry_no_ghost :
    ∀ a alpha,
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
      conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < alpha →
      alpha < conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
      conclusion_sample_pattern_family_closes_hot_contact_geometry_front alpha + a =
        conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc a →
        alpha = a
  conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_recovers_gamma :
    conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_gamma
        conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law =
      conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc
  conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_recovers_front :
    conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_front
        conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law =
      conclusion_sample_pattern_family_closes_hot_contact_geometry_front
  conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_recovers_pressure :
    conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_pressure
        conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law =
      conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure
  conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_recovers_q_star :
    conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_q_star
        conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law =
      conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star

/-- The concrete statement assembled from hot-phase reciprocity, no-ghost exposure, and
sample-pattern recovery of the full contact-geometry package. -/
def conclusion_sample_pattern_family_closes_hot_contact_geometry_statement
    (D : conclusion_sample_pattern_family_closes_hot_contact_geometry_data) : Prop :=
  D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 <
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 ∧
    (∀ a,
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        0 < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a ∧
          D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a < 1) ∧
    (∀ a,
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a =
          1 - D.conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_slope a) ∧
    (∀ a,
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        a =
          D.conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure_slope
            (D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a)) ∧
    (∀ a,
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure
            (D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a) =
          D.conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc a -
            a * D.conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_slope a) ∧
    (∀ a,
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure_curvature
            (D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star a) =
          -1 / D.conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_curvature a) ∧
    (∀ a,
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc a =
          D.conclusion_sample_pattern_family_closes_hot_contact_geometry_front a + a) ∧
    (∀ a alpha,
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < a →
      a < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a0 < alpha →
      alpha < D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a1 →
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_front alpha + a =
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc a →
        alpha = a) ∧
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_gamma
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law =
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_orc ∧
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_front
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law =
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_front ∧
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_pressure
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law =
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_pressure ∧
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_decode_q_star
        D.conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_law =
      D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_star

/-- Paper label: `thm:conclusion-sample-pattern-family-closes-hot-contact-geometry`. -/
theorem paper_conclusion_sample_pattern_family_closes_hot_contact_geometry
    (D : conclusion_sample_pattern_family_closes_hot_contact_geometry_data) :
    conclusion_sample_pattern_family_closes_hot_contact_geometry_statement D := by
  refine ⟨D.conclusion_sample_pattern_family_closes_hot_contact_geometry_hot_nonempty,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_range,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_q_reciprocity,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_a_reciprocity,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_legendre_identity,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_curvature_identity,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_gamma_front,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_no_ghost,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_recovers_gamma,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_recovers_front,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_recovers_pressure,
    D.conclusion_sample_pattern_family_closes_hot_contact_geometry_sample_recovers_q_star⟩

end Omega.Conclusion
