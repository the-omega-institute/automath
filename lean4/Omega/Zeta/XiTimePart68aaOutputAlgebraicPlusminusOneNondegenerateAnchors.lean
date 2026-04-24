import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Omega.Zeta

/-- The closed form `Q(1,u) = -u (u - 4) (u - 1) (u + 1)`. -/
def xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_one (u : ℝ) : ℝ :=
  -u * (u - 4) * (u - 1) * (u + 1)

/-- The closed form `Q(-1,u) = -(u - 1)^2 (u^2 + 6u - 2)`. -/
def xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_neg_one
    (u : ℝ) : ℝ :=
  -((u - 1) ^ (2 : ℕ)) * (u ^ (2 : ℕ) + 6 * u - 2)

/-- The factorization `Δ(1,u) = (1 - u) Q(1,u)`. -/
def xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Delta_at_one
    (u : ℝ) : ℝ :=
  (1 - u) *
    xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_one u

/-- The factorization `Δ(-1,u) = (1 - u) Q(-1,u)`. -/
def xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Delta_at_neg_one
    (u : ℝ) : ℝ :=
  (1 - u) *
    xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_neg_one u

/-- The positive-real collision parameters enumerated in the paper discussion around `u = 1`. -/
def xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_positive_real_collision_set
    (u : ℝ) : Prop :=
  u = 0.0084602654608787966132 ∨
    u = 0.74553449580298956225 ∨
    u = 0.93283726248596492776 ∨
    u = 1.0547964213679192275 ∨
    u = 2.0903923780490870311 ∨
    u = 15.522820704426852031

private lemma xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_u_minus_bounds :
    (31 : ℝ) / 100 < -3 + Real.sqrt 11 ∧ -3 + Real.sqrt 11 < (8 : ℝ) / 25 := by
  have hsqrt_sq : (Real.sqrt 11 : ℝ) ^ (2 : ℕ) = 11 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 11 by positivity)]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 11 := by positivity
  have hlow_nonneg : 0 ≤ (331 : ℝ) / 100 := by positivity
  have hhigh_nonneg : 0 ≤ (83 : ℝ) / 25 := by positivity
  have hlow_sq : ((331 : ℝ) / 100) ^ (2 : ℕ) < 11 := by norm_num
  have hhigh_sq : 11 < ((83 : ℝ) / 25) ^ (2 : ℕ) := by norm_num
  have hlow : (331 : ℝ) / 100 < Real.sqrt 11 := by
    nlinarith [hlow_sq, hsqrt_sq, hsqrt_nonneg, hlow_nonneg]
  have hhigh : Real.sqrt 11 < (83 : ℝ) / 25 := by
    nlinarith [hhigh_sq, hsqrt_sq, hsqrt_nonneg, hhigh_nonneg]
  constructor <;> nlinarith

/-- Paper label: `thm:xi-time-part68aa-output-algebraic-plusminus-one-nondegenerate-anchors`.

The exact evaluations `Q(1,4) = 0` and `Q(-1,-3 + √11) = 0`, together with
`Δ(±1,u) = (1 - u) Q(±1,u)`, produce algebraic positive-real anchors for the eigenvalues
`λ = ±1`.  The same two parameters lie outside the enumerated positive-real collision set, so the
anchors are nondegenerate. -/
theorem paper_xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors :
    xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_one 4 = 0 ∧
      xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_neg_one
          (-3 + Real.sqrt 11) = 0 ∧
      xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Delta_at_one 4 = 0 ∧
      xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Delta_at_neg_one
          (-3 + Real.sqrt 11) = 0 ∧
      0 < (4 : ℝ) ∧
      0 < -3 + Real.sqrt 11 ∧
      ¬ xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_positive_real_collision_set
          4 ∧
      ¬ xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_positive_real_collision_set
          (-3 + Real.sqrt 11) := by
  have hsqrt11 : (Real.sqrt 11 : ℝ) ^ (2 : ℕ) = 11 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 11 by positivity)]
  have hQplus :
      xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_one 4 = 0 := by
    simp [xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_one]
  have hQminus :
      xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_neg_one
          (-3 + Real.sqrt 11) = 0 := by
    unfold xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Q_at_neg_one
    nlinarith
  have hposMinus : 0 < -3 + Real.sqrt 11 := by
    rcases
      xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_u_minus_bounds with
      ⟨hlow, _⟩
    nlinarith
  have hnotCollisionPlus :
      ¬ xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_positive_real_collision_set
          4 := by
    intro h
    rcases h with h | h | h | h | h | h <;> norm_num at h
  have hnotCollisionMinus :
      ¬ xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_positive_real_collision_set
          (-3 + Real.sqrt 11) := by
    intro h
    rcases
      xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_u_minus_bounds with
      ⟨hlow, hhigh⟩
    rcases h with h | h | h | h | h | h <;> nlinarith
  refine ⟨hQplus, hQminus, ?_, ?_, by positivity, hposMinus, hnotCollisionPlus,
    hnotCollisionMinus⟩
  · simp [xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Delta_at_one,
      hQplus]
  · simp [xi_time_part68aa_output_algebraic_plusminus_one_nondegenerate_anchors_Delta_at_neg_one,
      hQminus]

end Omega.Zeta
