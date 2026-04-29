import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Conclusion.SerrinRealizableMeanConeCollapse

namespace Omega.Conclusion

open scoped BigOperators

/-- The collapsed admissible pressure envelope on the normalized Serrin realizable class. -/
def conclusion_serrin_realizable_thermodynamic_frontier_affine_pressure {d : ℕ}
    (θ v : Fin d → ℝ) : ℝ :=
  ∑ i, θ i * v i

noncomputable section

/-- The Legendre-Fenchel dual of the affine pressure envelope: the indicator of the singleton
frontier point. -/
noncomputable def conclusion_serrin_realizable_thermodynamic_frontier_affine_dual {d : ℕ}
    (v x : Fin d → ℝ) : WithTop ℝ :=
  if x = v then 0 else ⊤

lemma conclusion_serrin_realizable_thermodynamic_frontier_affine_positive_ray_witness
    {n d : ℕ} (vWK : Fin d → ℝ) :
    Set.range (conclusion_serrin_realizable_mean_cone_collapse_observable (n := n) vWK) =
      conclusion_serrin_realizable_mean_cone_collapse_positive_ray vWK := by
  ext w
  constructor
  · rintro ⟨Ω, rfl⟩
    exact ⟨Ω.2.1, Ω.2.2, rfl⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨(0, ⟨ρ, hρ⟩), by
      simp [conclusion_serrin_realizable_mean_cone_collapse_observable]⟩

lemma conclusion_serrin_realizable_thermodynamic_frontier_affine_normalized_image_singleton
    {n d : ℕ} (WK : Fin n → ℝ) (vWK : Fin d → ℝ) (hvWK : vWK ≠ 0) :
    conclusion_serrin_realizable_mean_cone_collapse_normalized_image (n := n) vWK = {vWK} := by
  have hcollapse :=
    paper_conclusion_serrin_realizable_mean_cone_collapse (n := n) (d := d) WK vWK hvWK
  rcases hcollapse.2.2 with ⟨v, hv, hvuniq⟩
  have hvWKprop :
      vWK ≠ 0 ∧
        Set.range (conclusion_serrin_realizable_mean_cone_collapse_observable (n := n) vWK) =
          conclusion_serrin_realizable_mean_cone_collapse_positive_ray vWK ∧
        conclusion_serrin_realizable_mean_cone_collapse_normalized_image (n := n) vWK = {vWK} := by
    refine ⟨hvWK,
      conclusion_serrin_realizable_thermodynamic_frontier_affine_positive_ray_witness
        (n := n) vWK,
      ?_⟩
    ext w
    constructor
    · rintro ⟨x0, rfl⟩
      simp [conclusion_serrin_realizable_mean_cone_collapse_observable]
    · rintro rfl
      exact ⟨0, by simp [conclusion_serrin_realizable_mean_cone_collapse_observable]⟩
  have hv_eq : vWK = v := hvuniq vWK hvWKprop
  simpa [hv_eq] using hv.2.2

/-- Paper-facing thermodynamic frontier package for the normalized realizable Serrin class. -/
def conclusion_serrin_realizable_thermodynamic_frontier_affine_statement : Prop :=
  ∀ {n d : ℕ} (WK : Fin n → ℝ) (vWK : Fin d → ℝ), vWK ≠ 0 →
    (∀ Ω : conclusion_serrin_realizable_mean_cone_collapse_domain n,
      conclusion_serrin_realizable_mean_cone_collapse_representative WK Ω =
        Ω.1 + Ω.2.1 • WK) ∧
    conclusion_serrin_realizable_mean_cone_collapse_normalized_image (n := n) vWK = {vWK} ∧
    (∀ θ : Fin d → ℝ,
      conclusion_serrin_realizable_thermodynamic_frontier_affine_pressure θ vWK =
        ∑ i, θ i * vWK i) ∧
    (∀ x : Fin d → ℝ,
      conclusion_serrin_realizable_thermodynamic_frontier_affine_dual vWK x =
        if x = vWK then 0 else ⊤)

theorem paper_conclusion_serrin_realizable_thermodynamic_frontier_affine :
    conclusion_serrin_realizable_thermodynamic_frontier_affine_statement := by
  intro n d WK vWK hvWK
  have hcollapse :=
    paper_conclusion_serrin_realizable_mean_cone_collapse (n := n) (d := d) WK vWK hvWK
  refine ⟨
    hcollapse.1,
    conclusion_serrin_realizable_thermodynamic_frontier_affine_normalized_image_singleton
      WK vWK hvWK,
    ?_,
    ?_⟩
  · intro θ
    rfl
  · intro x
    by_cases hx : x = vWK
    · simp [conclusion_serrin_realizable_thermodynamic_frontier_affine_dual, hx]
    · simp [conclusion_serrin_realizable_thermodynamic_frontier_affine_dual, hx]

end

end Omega.Conclusion
