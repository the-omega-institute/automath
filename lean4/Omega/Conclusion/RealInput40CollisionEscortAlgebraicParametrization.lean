import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Set.Function
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete data for the real-input-`40` escort parametrization. -/
structure conclusion_realinput40_collision_escort_algebraic_parametrization_data where

namespace conclusion_realinput40_collision_escort_algebraic_parametrization_data

/-- Left endpoint of the admissible `ρ`-interval. -/
def conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar
    (_D : conclusion_realinput40_collision_escort_algebraic_parametrization_data) : ℝ :=
  1 + Real.sqrt 2

/-- Explicit inverse parameter `u(ρ) = ρ - (1 + √2)`. -/
def conclusion_realinput40_collision_escort_algebraic_parametrization_u
    (D : conclusion_realinput40_collision_escort_algebraic_parametrization_data) (ρ : ℝ) : ℝ :=
  ρ - D.conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar

/-- Escort parameter `α(ρ) = u / (2 (1 + u))`, mapping `(1 + √2, ∞)` onto `(0, 1/2)`. -/
def conclusion_realinput40_collision_escort_algebraic_parametrization_alpha
    (D : conclusion_realinput40_collision_escort_algebraic_parametrization_data) (ρ : ℝ) : ℝ :=
  D.conclusion_realinput40_collision_escort_algebraic_parametrization_u ρ /
    (2 * (1 + D.conclusion_realinput40_collision_escort_algebraic_parametrization_u ρ))

/-- The explicit `u(ρ)` inverts the affine shift from the endpoint `1 + √2`. -/
def uRhoInverse
    (D : conclusion_realinput40_collision_escort_algebraic_parametrization_data) : Prop :=
  ∀ ρ,
    D.conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar ≤ ρ →
      D.conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar +
          D.conclusion_realinput40_collision_escort_algebraic_parametrization_u ρ = ρ

/-- The escort parameter is the explicit rational function of `u(ρ)`. -/
def alphaExplicit
    (D : conclusion_realinput40_collision_escort_algebraic_parametrization_data) : Prop :=
  ∀ ρ,
    D.conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar ≤ ρ →
      D.conclusion_realinput40_collision_escort_algebraic_parametrization_alpha ρ =
        D.conclusion_realinput40_collision_escort_algebraic_parametrization_u ρ /
          (2 * (1 + D.conclusion_realinput40_collision_escort_algebraic_parametrization_u ρ))

/-- Strict monotonicity of the escort parameter on the admissible half-line. -/
def alphaStrictMono
    (D : conclusion_realinput40_collision_escort_algebraic_parametrization_data) : Prop :=
  StrictMonoOn D.conclusion_realinput40_collision_escort_algebraic_parametrization_alpha
    (Set.Ici D.conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar)

/-- The escort parameter maps the open half-line `(1 + √2, ∞)` bijectively onto `(0, 1/2)`. -/
def alphaRange
    (D : conclusion_realinput40_collision_escort_algebraic_parametrization_data) : Prop :=
  Set.MapsTo D.conclusion_realinput40_collision_escort_algebraic_parametrization_alpha
      (Set.Ioi D.conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar)
      (Set.Ioo (0 : ℝ) (1 / 2)) ∧
    ∀ y ∈ Set.Ioo (0 : ℝ) (1 / 2),
      ∃ ρ ∈ Set.Ioi D.conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar,
        D.conclusion_realinput40_collision_escort_algebraic_parametrization_alpha ρ = y

end conclusion_realinput40_collision_escort_algebraic_parametrization_data

open conclusion_realinput40_collision_escort_algebraic_parametrization_data

/-- Paper label: `thm:conclusion-realinput40-collision-escort-algebraic-parametrization`. -/
theorem paper_conclusion_realinput40_collision_escort_algebraic_parametrization
    (D : conclusion_realinput40_collision_escort_algebraic_parametrization_data) :
    D.uRhoInverse ∧ D.alphaExplicit ∧ D.alphaStrictMono ∧ D.alphaRange := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold uRhoInverse
    intro ρ hρ
    change (1 + Real.sqrt 2) + (ρ - (1 + Real.sqrt 2)) = ρ
    ring
  · unfold alphaExplicit
    intro ρ hρ
    rfl
  · unfold alphaStrictMono
    intro x hx y hy hxy
    change (x - (1 + Real.sqrt 2)) / (2 * (1 + (x - (1 + Real.sqrt 2)))) <
      (y - (1 + Real.sqrt 2)) / (2 * (1 + (y - (1 + Real.sqrt 2))))
    have hx0 : 0 ≤ x - (1 + Real.sqrt 2) := sub_nonneg.mpr hx
    have hy0 : 0 ≤ y - (1 + Real.sqrt 2) := sub_nonneg.mpr hy
    have hdenx : 0 < 2 * (1 + (x - (1 + Real.sqrt 2))) := by nlinarith
    have hdeny : 0 < 2 * (1 + (y - (1 + Real.sqrt 2))) := by nlinarith
    exact (div_lt_div_iff₀ hdenx hdeny).2 <| by
      nlinarith [sub_lt_sub_right hxy (1 + Real.sqrt 2)]
  · unfold alphaRange
    refine ⟨?_, ?_⟩
    · intro ρ hρ
      constructor
      · change 0 < (ρ - (1 + Real.sqrt 2)) / (2 * (1 + (ρ - (1 + Real.sqrt 2))))
        have ht : 0 < ρ - (1 + Real.sqrt 2) := sub_pos.mpr hρ
        have hden : 0 < 2 * (1 + (ρ - (1 + Real.sqrt 2))) := by nlinarith
        exact div_pos ht hden
      · change (ρ - (1 + Real.sqrt 2)) / (2 * (1 + (ρ - (1 + Real.sqrt 2)))) < 1 / 2
        have ht : 0 < ρ - (1 + Real.sqrt 2) := sub_pos.mpr hρ
        have hden : 0 < 2 * (1 + (ρ - (1 + Real.sqrt 2))) := by
          nlinarith
        have htwo : (0 : ℝ) < 2 := by norm_num
        exact (div_lt_div_iff₀ hden htwo).2 <| by
          nlinarith
    · intro y hy
      refine ⟨D.conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar +
          (2 * y) / (1 - 2 * y), ?_, ?_⟩
      · change 1 + Real.sqrt 2 < (1 + Real.sqrt 2) + (2 * y) / (1 - 2 * y)
        have hy_pos : 0 < y := hy.1
        have hden_pos : 0 < 1 - 2 * y := by nlinarith [hy.2]
        have hfrac_pos : 0 < (2 * y) / (1 - 2 * y) := by
          have hnum_pos : 0 < 2 * y := by linarith
          exact div_pos hnum_pos hden_pos
        linarith
      · dsimp [conclusion_realinput40_collision_escort_algebraic_parametrization_alpha,
          conclusion_realinput40_collision_escort_algebraic_parametrization_u,
          conclusion_realinput40_collision_escort_algebraic_parametrization_rhoStar]
        have hden_pos : 0 < 1 - 2 * y := by nlinarith [hy.2]
        have hden_ne : 1 - 2 * y ≠ 0 := ne_of_gt hden_pos
        field_simp [hden_ne]
        ring

end

end Omega.Conclusion
