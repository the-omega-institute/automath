import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

structure conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data where
  F : ℕ
  hF : 0 < F
  m : ℕ
  multiplicity : Fin F → ℝ

namespace conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_mass
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : ℝ :=
  (2 : ℝ) ^ D.m

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : ℝ :=
  D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_mass / D.F

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_zeroIndex
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : Fin D.F :=
  ⟨0, D.hF⟩

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) (r : Fin D.F) : ℝ :=
  D.multiplicity r - D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : ℝ :=
  Finset.sup' Finset.univ ⟨D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_zeroIndex,
    by simp [conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_zeroIndex]⟩
    (fun r => |D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered r|)

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : ℝ :=
  (D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias /
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average) ^ (2 : ℕ)

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : Prop :=
  ∀ r : Fin D.F,
    D.multiplicity r = D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierCoeff
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) (r : Fin D.F) : ℝ :=
  D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered r

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_twistedGhost
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) (r : Fin D.F) : ℝ :=
  D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierCoeff r

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierVanish
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : Prop :=
  ∀ r : Fin D.F,
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierCoeff r = 0

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_twistedGhostVanish
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : Prop :=
  ∀ r : Fin D.F,
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_twistedGhost r = 0

def conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_spec
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) : Prop :=
  D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias ≥
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average *
        Real.sqrt D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap ∧
    (D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap = 0 ↔
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform) ∧
    (D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform ↔
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierVanish) ∧
    (D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierVanish ↔
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_twistedGhostVanish)

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average_pos
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    0 < D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average := by
  unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average
    conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_mass
  have hmass : 0 < (2 : ℝ) ^ D.m := by positivity
  have hF : (0 : ℝ) < D.F := by exact_mod_cast D.hF
  exact div_pos hmass hF

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average_nonneg
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    0 ≤ D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average := by
  exact le_of_lt <| D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average_pos

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_sup_dominates
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) (r : Fin D.F) :
    |D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered r| ≤
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias := by
  unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias
  exact Finset.le_sup'
    (s := (Finset.univ : Finset (Fin D.F)))
    (f := fun x => |D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered x|)
    (Finset.mem_univ r)

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias_nonneg
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    0 ≤ D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias := by
  let r0 := D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_zeroIndex
  exact le_trans (abs_nonneg _) <|
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_sup_dominates r0

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias_eq_zero_iff
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias = 0 ↔
      ∀ r : Fin D.F,
        D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered r = 0 := by
  constructor
  · intro hsup r
    have hle :=
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_sup_dominates r
    rw [hsup] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · intro hcentered
    refine le_antisymm ?_ D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias_nonneg
    unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias
    simp [hcentered]

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform_iff_centered_zero
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform ↔
      ∀ r : Fin D.F,
        D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered r = 0 := by
  constructor
  · intro hunif r
    unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered
    rw [hunif r]
    ring
  · intro hcentered r
    unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered at hcentered
    linarith [hcentered r]

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap_nonneg
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    0 ≤ D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap := by
  unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap
  positivity

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap_zero_iff_uniform
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap = 0 ↔
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform := by
  constructor
  · intro hgap
    have hratio :
        D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias /
            D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average = 0 := by
      exact sq_eq_zero_iff.mp hgap
    have hsup :
        D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias = 0 := by
      rcases (div_eq_zero_iff).mp hratio with hsup | havg
      · exact hsup
      · exact False.elim
          (D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average_pos.ne havg.symm)
    exact
      (D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform_iff_centered_zero).2
        ((D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias_eq_zero_iff).1 hsup)
  · intro hunif
    have hsup :
        D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias = 0 := by
      exact
        (D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias_eq_zero_iff).2
          ((D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform_iff_centered_zero).1
            hunif)
    unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap
    simp [hsup]

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform_iff_fourier
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform ↔
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierVanish := by
  constructor
  · intro hunif r
    unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierCoeff
      conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_centered
    rw [hunif r]
    ring
  · intro hfourier
    exact
      (D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform_iff_centered_zero).2
        hfourier

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourier_iff_twisted
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierVanish ↔
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_twistedGhostVanish := by
  constructor <;> intro h r <;>
    simpa [conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_twistedGhost,
      conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourierCoeff] using h r

lemma conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_lower_bound
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias ≥
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average *
        Real.sqrt D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap := by
  have hdiv_nonneg :
      0 ≤ D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias /
        D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average := by
    exact div_nonneg
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_supnormBias_nonneg
      D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average_nonneg
  unfold conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdiv_nonneg]
  field_simp [show
    D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average ≠ 0 by
      exact D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_average_pos.ne']
  exact le_rfl

end conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data

open conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data

theorem paper_conclusion_unified_ghost_yardstick_zero_test_supnorm_bias
    (D : conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_data) :
    conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_spec D := by
  refine ⟨D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_lower_bound, ?_, ?_, ?_⟩
  · exact D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_collisionGap_zero_iff_uniform
  · exact D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_uniform_iff_fourier
  · exact D.conclusion_unified_ghost_yardstick_zero_test_supnorm_bias_fourier_iff_twisted

end

end Omega.Conclusion
