import Mathlib.Tactic
import Omega.Zeta.XiTimePart62afCrossAnomInteractionDegree

namespace Omega.Zeta

/-- Concrete arity token for the MOM-scaling interaction-degree rigidity package. -/
abbrev xi_time_part62af_moment_interaction_degree_rigidity_data :=
  xi_time_part62af_cross_anom_interaction_degree_data

namespace xi_time_part62af_moment_interaction_degree_rigidity_data

/-- Scalar MOM-rescaling of a finite product-character observable. -/
def xi_time_part62af_moment_interaction_degree_rigidity_momScale
    (D : xi_time_part62af_moment_interaction_degree_rigidity_data) (c : ℤ)
    (f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ) :
    xi_time_part62af_cross_anom_interaction_degree_character D → ℤ :=
  fun χ => c * f χ

/-- Concrete statement: nonzero scalar MOM-rescaling pulls out of every Möbius difference,
therefore it preserves exactly the nonzero supports and the interaction degree. -/
noncomputable def xi_time_part62af_moment_interaction_degree_rigidity_statement
    (D : xi_time_part62af_moment_interaction_degree_rigidity_data) : Prop :=
  ∀ (c : ℤ), c ≠ 0 →
    ∀ f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ,
      (∀ (S : Finset (Fin D)) (χ : xi_time_part62af_cross_anom_interaction_degree_character D),
        xi_time_part62af_cross_anom_interaction_degree_anomaly D
            (D.xi_time_part62af_moment_interaction_degree_rigidity_momScale c f) S χ =
          c * xi_time_part62af_cross_anom_interaction_degree_anomaly D f S χ) ∧
      (∀ S : Finset (Fin D),
        xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D
            (D.xi_time_part62af_moment_interaction_degree_rigidity_momScale c f) S ↔
          xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D f S) ∧
      xi_time_part62af_cross_anom_interaction_degree_degree D
          (D.xi_time_part62af_moment_interaction_degree_rigidity_momScale c f) =
        xi_time_part62af_cross_anom_interaction_degree_degree D f

end xi_time_part62af_moment_interaction_degree_rigidity_data

open xi_time_part62af_moment_interaction_degree_rigidity_data

private lemma xi_time_part62af_moment_interaction_degree_rigidity_anomaly_scale
    (D : xi_time_part62af_moment_interaction_degree_rigidity_data) (c : ℤ)
    (f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ)
    (S : Finset (Fin D)) (χ : xi_time_part62af_cross_anom_interaction_degree_character D) :
    xi_time_part62af_cross_anom_interaction_degree_anomaly D
        (D.xi_time_part62af_moment_interaction_degree_rigidity_momScale c f) S χ =
      c * xi_time_part62af_cross_anom_interaction_degree_anomaly D f S χ := by
  rw [xi_time_part62af_cross_anom_interaction_degree_anomaly,
    xi_time_part62af_cross_anom_interaction_degree_anomaly, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _hT
  simp [xi_time_part62af_moment_interaction_degree_rigidity_momScale]
  ring

private lemma xi_time_part62af_moment_interaction_degree_rigidity_nonzeroSupport_iff
    (D : xi_time_part62af_moment_interaction_degree_rigidity_data) {c : ℤ} (hc : c ≠ 0)
    (f : xi_time_part62af_cross_anom_interaction_degree_character D → ℤ)
    (S : Finset (Fin D)) :
    xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D
        (D.xi_time_part62af_moment_interaction_degree_rigidity_momScale c f) S ↔
      xi_time_part62af_cross_anom_interaction_degree_nonzeroSupport D f S := by
  constructor
  · rintro ⟨χ, hχ⟩
    refine ⟨χ, ?_⟩
    intro hzero
    apply hχ
    rw [xi_time_part62af_moment_interaction_degree_rigidity_anomaly_scale, hzero]
    simp
  · rintro ⟨χ, hχ⟩
    refine ⟨χ, ?_⟩
    rw [xi_time_part62af_moment_interaction_degree_rigidity_anomaly_scale]
    exact mul_ne_zero hc hχ

/-- Paper label: `thm:xi-time-part62af-moment-interaction-degree-rigidity`. -/
theorem paper_xi_time_part62af_moment_interaction_degree_rigidity
    (D : xi_time_part62af_moment_interaction_degree_rigidity_data) :
    D.xi_time_part62af_moment_interaction_degree_rigidity_statement := by
  classical
  intro c hc f
  refine ⟨?_, ?_, ?_⟩
  · exact xi_time_part62af_moment_interaction_degree_rigidity_anomaly_scale D c f
  · intro S
    exact xi_time_part62af_moment_interaction_degree_rigidity_nonzeroSupport_iff D hc f S
  · unfold xi_time_part62af_cross_anom_interaction_degree_degree
    congr 1
    ext S
    simp [xi_time_part62af_moment_interaction_degree_rigidity_nonzeroSupport_iff D hc f S]

end Omega.Zeta
