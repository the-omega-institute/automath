import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic
import Omega.Core.OdometerJoukowsky

namespace Omega.GroupUnification

/-- Explicit real-parameter ellipse point attached to the Joukowsky radius parameter `u`. -/
noncomputable def groupJGJoukowskyEllipsePoint (u θ : ℝ) : ℂ :=
  (((Real.exp u + Real.exp (-u)) * Real.cos θ : ℝ) : ℂ) +
    (((Real.exp u - Real.exp (-u)) * Real.sin θ : ℝ) : ℂ) * Complex.I

private lemma groupJGJoukowsky_degenerate_formula (θ : ℝ) :
    groupJGJoukowskyEllipsePoint 0 θ = (2 * Real.cos θ : ℂ) := by
  calc
    groupJGJoukowskyEllipsePoint 0 θ
        = ((((Real.exp 0 + Real.exp (-0)) * Real.cos θ : ℝ) : ℂ) +
            ((((Real.exp 0 - Real.exp (-0)) * Real.sin θ : ℝ) : ℂ) * Complex.I)) := by
              rfl
    _ = ((((1 + 1) * Real.cos θ : ℝ) : ℂ) + (((0 : ℝ) : ℂ) * Complex.I)) := by
          simp
    _ = (2 * Real.cos θ : ℂ) := by
          norm_num

private lemma groupJGJoukowsky_unit_segment_hit (θ : ℝ) :
    ∃ t : ℝ, t ∈ Set.Icc (-2) 2 ∧ groupJGJoukowskyEllipsePoint 0 θ = (t : ℂ) := by
  refine ⟨2 * Real.cos θ, ?_, ?_⟩
  constructor <;> linarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  simpa using groupJGJoukowsky_degenerate_formula θ

private lemma groupJGJoukowsky_unit_segment_surj (t : ℝ) (ht : t ∈ Set.Icc (-2) 2) :
    ∃ θ : ℝ, groupJGJoukowskyEllipsePoint 0 θ = (t : ℂ) := by
  refine ⟨Real.arccos (t / 2), ?_⟩
  rw [groupJGJoukowsky_degenerate_formula]
  have hcos : Real.cos (Real.arccos (t / 2)) = t / 2 := by
    apply Real.cos_arccos
    · linarith [ht.1, ht.2]
    · linarith [ht.1, ht.2]
  rw [hcos]
  have htwo : (2 : ℝ) * (t / 2) = t := by ring
  exact_mod_cast htwo

private lemma groupJGJoukowsky_quadratic (y : ℂ) (hy : y ≠ 0) :
    y ^ 2 - Omega.POM.joukowsky y * y + 1 = 0 := by
  unfold Omega.POM.joukowsky
  field_simp [hy]
  ring

private lemma groupJGJoukowsky_nonunit_not_fixed (u : ℝ) (hu : u ≠ 0) {y : ℂ}
    (hyR : ‖y‖ = Real.exp u) :
    y ≠ y⁻¹ := by
  intro hInv
  have hnorm : Real.exp u = (Real.exp u)⁻¹ := by
    calc
      Real.exp u = ‖y‖ := hyR.symm
      _ = ‖y⁻¹‖ := by rw [← hInv]
      _ = ‖y‖⁻¹ := by rw [norm_inv]
      _ = (Real.exp u)⁻¹ := by rw [hyR]
  have hExp0 : (Real.exp u : ℝ) ≠ 0 := by positivity
  have hmul' := congrArg (fun t : ℝ => t * Real.exp u) hnorm
  have hmul : Real.exp u * Real.exp u = 1 := by
    simpa [hExp0, mul_assoc] using hmul'
  have hExp : Real.exp (u + u) = 1 := by
    simpa [Real.exp_add] using hmul
  have hsum : u + u = 0 := by rwa [Real.exp_eq_one_iff] at hExp
  have hu0 : u = 0 := by linarith
  exact hu hu0

private lemma groupJGJoukowsky_unit_fixed_points (y : ℂ) (hy : ‖y‖ = 1) :
    y = y⁻¹ ↔ y = 1 ∨ y = -1 := by
  have hy0 : y ≠ 0 := by
    intro hy0
    have : ‖(0 : ℂ)‖ = 1 := by simpa [hy0] using hy
    norm_num at this
  constructor
  · intro hInv
    have hySq : y * y = 1 := by
      have hmul := congrArg (fun z : ℂ => z * y) hInv
      simpa [hy0, mul_assoc] using hmul
    have hfac : (y - 1) * (y + 1) = 0 := by
      calc
        (y - 1) * (y + 1) = y * y - 1 := by ring
        _ = 0 := by simpa using sub_eq_zero.mpr hySq
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr ((eq_neg_iff_add_eq_zero).2 h2)
  · rintro (rfl | rfl) <;> simp

/-- The explicit Joukowsky ellipse parameterization degenerates at `u = 0` to the segment
`[-2, 2]`; the quadratic relation `y² - wy + 1 = 0` and inversion symmetry `y ↔ y⁻¹`
distinguish the non-unit embedded layers from the unit-circle branch points `y = ±1`.
    prop:group-jg-joukowsky-degenerate-branch-segment -/
theorem paper_group_jg_joukowsky_degenerate_branch_segment :
    (∀ u θ : ℝ,
      groupJGJoukowskyEllipsePoint u θ =
        (((Real.exp u + Real.exp (-u)) * Real.cos θ : ℝ) : ℂ) +
          (((Real.exp u - Real.exp (-u)) * Real.sin θ : ℝ) : ℂ) * Complex.I) ∧
    (∀ θ : ℝ, groupJGJoukowskyEllipsePoint 0 θ = (2 * Real.cos θ : ℂ)) ∧
    (∀ θ : ℝ,
      ∃ t : ℝ, t ∈ Set.Icc (-2) 2 ∧ groupJGJoukowskyEllipsePoint 0 θ = (t : ℂ)) ∧
    (∀ t : ℝ, t ∈ Set.Icc (-2) 2 → ∃ θ : ℝ, groupJGJoukowskyEllipsePoint 0 θ = (t : ℂ)) ∧
    (∀ y : ℂ, y ≠ 0 →
      y ^ 2 - Omega.POM.joukowsky y * y + 1 = 0 ∧
        Omega.POM.joukowsky y = Omega.POM.joukowsky y⁻¹) ∧
    (∀ u : ℝ, u ≠ 0 → ∀ y : ℂ, ‖y‖ = Real.exp u → y ≠ y⁻¹) ∧
    (∀ y : ℂ, ‖y‖ = 1 → (y = y⁻¹ ↔ y = 1 ∨ y = -1)) := by
  refine ⟨?_, groupJGJoukowsky_degenerate_formula, groupJGJoukowsky_unit_segment_hit,
    groupJGJoukowsky_unit_segment_surj, ?_, ?_, ?_⟩
  · intro u θ
    rfl
  · intro y hy
    exact ⟨groupJGJoukowsky_quadratic y hy, Omega.POM.joukowsky_symmetric y hy⟩
  · intro u hu y hyR
    exact groupJGJoukowsky_nonunit_not_fixed u hu hyR
  · intro y hy
    exact groupJGJoukowsky_unit_fixed_points y hy

end Omega.GroupUnification
