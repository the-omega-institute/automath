import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- A concrete weighted free commutative monoid model on one generator. -/
abbrev conclusion_weighted_free_cmon_metric_rigidity_model := ℕ

/-- The radius from zero in the weight-`φ` model. -/
def conclusion_weighted_free_cmon_metric_rigidity_radius
    (x : conclusion_weighted_free_cmon_metric_rigidity_model) : ℝ :=
  Real.goldenRatio * x

/-- Weighted `ℓ¹` metric on the free commutative monoid `ℕ`. -/
def conclusion_weighted_free_cmon_metric_rigidity_dist
    (x y : conclusion_weighted_free_cmon_metric_rigidity_model) : ℝ :=
  Real.goldenRatio * |(x : ℝ) - y|

/-- A center has injective profile when its distance-to-center function is injective. -/
def conclusion_weighted_free_cmon_metric_rigidity_center_has_injective_profile
    (u : conclusion_weighted_free_cmon_metric_rigidity_model) : Prop :=
  Function.Injective (fun x => conclusion_weighted_free_cmon_metric_rigidity_dist u x)

/-- Chapter-local self-isometries are bijections preserving the weighted metric exactly. -/
def conclusion_weighted_free_cmon_metric_rigidity_isometry
    (F : conclusion_weighted_free_cmon_metric_rigidity_model →
      conclusion_weighted_free_cmon_metric_rigidity_model) : Prop :=
  Function.Bijective F ∧
    ∀ x y,
      conclusion_weighted_free_cmon_metric_rigidity_dist (F x) (F y) =
        conclusion_weighted_free_cmon_metric_rigidity_dist x y

/-- Paper-facing rigidity package for the weighted free commutative monoid model: zero is the
unique center with injective radius profile, every self-isometry fixes zero and hence every
point, and addition is the unique element with additive radius. -/
def conclusion_weighted_free_cmon_metric_rigidity_statement : Prop :=
  (∃! u : conclusion_weighted_free_cmon_metric_rigidity_model,
    conclusion_weighted_free_cmon_metric_rigidity_center_has_injective_profile u) ∧
    (∀ F,
      conclusion_weighted_free_cmon_metric_rigidity_isometry F →
        F = id) ∧
    (∀ x y : conclusion_weighted_free_cmon_metric_rigidity_model,
      ∃! z : conclusion_weighted_free_cmon_metric_rigidity_model,
        conclusion_weighted_free_cmon_metric_rigidity_radius z =
          conclusion_weighted_free_cmon_metric_rigidity_radius x +
            conclusion_weighted_free_cmon_metric_rigidity_radius y)

private theorem conclusion_weighted_free_cmon_metric_rigidity_dist_zero_eq_radius
    (x : conclusion_weighted_free_cmon_metric_rigidity_model) :
    conclusion_weighted_free_cmon_metric_rigidity_dist 0 x =
      conclusion_weighted_free_cmon_metric_rigidity_radius x := by
  simp [conclusion_weighted_free_cmon_metric_rigidity_dist,
    conclusion_weighted_free_cmon_metric_rigidity_radius, abs_of_nonpos]

private theorem conclusion_weighted_free_cmon_metric_rigidity_radius_injective :
    Function.Injective conclusion_weighted_free_cmon_metric_rigidity_radius := by
  intro x y hxy
  dsimp [conclusion_weighted_free_cmon_metric_rigidity_radius] at hxy
  have hphi_ne : (Real.goldenRatio : ℝ) ≠ 0 := Real.goldenRatio_ne_zero
  exact_mod_cast (mul_left_cancel₀ hphi_ne hxy)

private theorem conclusion_weighted_free_cmon_metric_rigidity_zero_profile_injective :
    conclusion_weighted_free_cmon_metric_rigidity_center_has_injective_profile 0 := by
  intro x y hxy
  apply conclusion_weighted_free_cmon_metric_rigidity_radius_injective
  simpa [conclusion_weighted_free_cmon_metric_rigidity_dist_zero_eq_radius] using hxy

private theorem conclusion_weighted_free_cmon_metric_rigidity_nonzero_center_not_injective
    (u : conclusion_weighted_free_cmon_metric_rigidity_model) (hu : u ≠ 0) :
    ¬ conclusion_weighted_free_cmon_metric_rigidity_center_has_injective_profile u := by
  intro hinj
  have hupos : 0 < u := Nat.pos_of_ne_zero hu
  have hdist :
      conclusion_weighted_free_cmon_metric_rigidity_dist u 0 =
        conclusion_weighted_free_cmon_metric_rigidity_dist u (2 * u) := by
    have hleft : conclusion_weighted_free_cmon_metric_rigidity_dist u 0 = Real.goldenRatio * u := by
      simp [conclusion_weighted_free_cmon_metric_rigidity_dist, abs_of_nonneg]
    have hright :
        conclusion_weighted_free_cmon_metric_rigidity_dist u (2 * u) = Real.goldenRatio * u := by
      unfold conclusion_weighted_free_cmon_metric_rigidity_dist
      have hcast : ((2 * u : ℕ) : ℝ) = 2 * (u : ℝ) := by
        norm_num
      rw [hcast]
      have hle : (u : ℝ) - 2 * (u : ℝ) ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos hle]
      ring
    exact hleft.trans hright.symm
  have hzero : 0 = 2 * u := hinj hdist
  have hu_zero : u = 0 := by
    have hs : u + u = 0 := by
      simpa [two_mul] using hzero.symm
    exact (Nat.add_eq_zero_iff.mp hs).2
  exact hu hu_zero

private theorem conclusion_weighted_free_cmon_metric_rigidity_zero_unique :
    ∃! u : conclusion_weighted_free_cmon_metric_rigidity_model,
      conclusion_weighted_free_cmon_metric_rigidity_center_has_injective_profile u := by
  refine ⟨0, conclusion_weighted_free_cmon_metric_rigidity_zero_profile_injective, ?_⟩
  intro u hu
  by_contra hne
  exact conclusion_weighted_free_cmon_metric_rigidity_nonzero_center_not_injective u hne hu

private theorem conclusion_weighted_free_cmon_metric_rigidity_radius_add
    (x y : conclusion_weighted_free_cmon_metric_rigidity_model) :
    conclusion_weighted_free_cmon_metric_rigidity_radius (x + y) =
      conclusion_weighted_free_cmon_metric_rigidity_radius x +
        conclusion_weighted_free_cmon_metric_rigidity_radius y := by
  simp [conclusion_weighted_free_cmon_metric_rigidity_radius, left_distrib]

theorem paper_conclusion_weighted_free_cmon_metric_rigidity :
    conclusion_weighted_free_cmon_metric_rigidity_statement := by
  rcases conclusion_weighted_free_cmon_metric_rigidity_zero_unique with ⟨u0, hu0, hu0_unique⟩
  refine ⟨conclusion_weighted_free_cmon_metric_rigidity_zero_unique, ?_, ?_⟩
  · intro F hF
    have hbij := hF.1
    have hdist_pres := hF.2
    have hcenter :
        conclusion_weighted_free_cmon_metric_rigidity_center_has_injective_profile (F 0) := by
      intro x y hxy
      obtain ⟨x', rfl⟩ := hbij.surjective x
      obtain ⟨y', rfl⟩ := hbij.surjective y
      have hback :
          conclusion_weighted_free_cmon_metric_rigidity_dist 0 x' =
            conclusion_weighted_free_cmon_metric_rigidity_dist 0 y' := by
        simpa [hdist_pres 0 x', hdist_pres 0 y'] using hxy
      have hpre : x' = y' :=
        conclusion_weighted_free_cmon_metric_rigidity_zero_profile_injective hback
      simpa [hpre]
    have hu0_eq_zero : u0 = 0 := by
      symm
      exact hu0_unique 0 conclusion_weighted_free_cmon_metric_rigidity_zero_profile_injective
    have hF0 : F 0 = 0 := by
      calc
        F 0 = u0 := hu0_unique _ hcenter
        _ = 0 := hu0_eq_zero
    funext x
    apply conclusion_weighted_free_cmon_metric_rigidity_radius_injective
    calc
      conclusion_weighted_free_cmon_metric_rigidity_radius (F x) =
          conclusion_weighted_free_cmon_metric_rigidity_dist 0 (F x) := by
            rw [← conclusion_weighted_free_cmon_metric_rigidity_dist_zero_eq_radius]
      _ = conclusion_weighted_free_cmon_metric_rigidity_dist (F 0) (F x) := by
            simpa [hF0]
      _ = conclusion_weighted_free_cmon_metric_rigidity_dist 0 x := hdist_pres 0 x
      _ = conclusion_weighted_free_cmon_metric_rigidity_radius x := by
            rw [conclusion_weighted_free_cmon_metric_rigidity_dist_zero_eq_radius]
  · intro x y
    refine ⟨x + y, conclusion_weighted_free_cmon_metric_rigidity_radius_add x y, ?_⟩
    intro z hz
    apply conclusion_weighted_free_cmon_metric_rigidity_radius_injective
    simpa [conclusion_weighted_free_cmon_metric_rigidity_radius_add x y] using hz

end

end Omega.Conclusion
