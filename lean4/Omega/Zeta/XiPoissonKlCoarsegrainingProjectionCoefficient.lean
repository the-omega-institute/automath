import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The normalized second-order score on the two-point seed model. -/
def xi_poisson_kl_coarsegraining_projection_coefficient_score : Fin 2 → ℝ
  | 0 => 1 / 2
  | 1 => -1 / 2

/-- The conditional expectation of the score under a two-point coarsegraining: if the two source
points are merged, the projected score is `0`; if they stay separated, the projected score is the
original score. -/
def xi_poisson_kl_coarsegraining_projection_coefficient_condexp
    (Φ : Fin 2 → Bool) : Fin 2 → ℝ :=
  if _h : Φ 0 = Φ 1 then
    0
  else
    xi_poisson_kl_coarsegraining_projection_coefficient_score

/-- The normalized squared `L²` norm on the two-point seed space. -/
def xi_poisson_kl_coarsegraining_projection_coefficient_l2_norm_sq
    (u : Fin 2 → ℝ) : ℝ :=
  ((u 0) ^ 2 + (u 1) ^ 2) / 2

/-- The second-order KL projection coefficient in the seed model. -/
def xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit
    (Φ : Fin 2 → Bool) : ℝ :=
  if _h : Φ 0 = Φ 1 then 0 else 1 / 8

/-- The score is measurable with respect to the coarsegraining if it is constant on the fibers of
the projection. -/
def xi_poisson_kl_coarsegraining_projection_coefficient_score_measurable
    (Φ : Fin 2 → Bool) : Prop :=
  ∀ i j : Fin 2, Φ i = Φ j →
    xi_poisson_kl_coarsegraining_projection_coefficient_score i =
      xi_poisson_kl_coarsegraining_projection_coefficient_score j

lemma xi_poisson_kl_coarsegraining_projection_coefficient_score_norm :
    xi_poisson_kl_coarsegraining_projection_coefficient_l2_norm_sq
        xi_poisson_kl_coarsegraining_projection_coefficient_score =
      1 / 4 := by
  norm_num [xi_poisson_kl_coarsegraining_projection_coefficient_l2_norm_sq,
    xi_poisson_kl_coarsegraining_projection_coefficient_score]

lemma xi_poisson_kl_coarsegraining_projection_coefficient_score_measurable_of_ne
    {Φ : Fin 2 → Bool} (hΦ : Φ 0 ≠ Φ 1) :
    xi_poisson_kl_coarsegraining_projection_coefficient_score_measurable Φ := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    exact hΦ hij
  · exfalso
    exact hΦ hij.symm
  · rfl

lemma xi_poisson_kl_coarsegraining_projection_coefficient_not_measurable_of_eq
    {Φ : Fin 2 → Bool} (hΦ : Φ 0 = Φ 1) :
    ¬ xi_poisson_kl_coarsegraining_projection_coefficient_score_measurable Φ := by
  intro hMeas
  have hScore :
      xi_poisson_kl_coarsegraining_projection_coefficient_score 0 =
        xi_poisson_kl_coarsegraining_projection_coefficient_score 1 :=
    hMeas 0 1 hΦ
  norm_num [xi_poisson_kl_coarsegraining_projection_coefficient_score] at hScore

/-- Proposition-level statement for the coarsegrained second-order Poisson KL coefficient: the KL
limit is half the squared `L²` norm of the conditional expectation of the score, it is bounded by
`1/8`, and equality is equivalent to measurability of the score with respect to the coarsegraining.
-/
def xi_poisson_kl_coarsegraining_projection_coefficient_statement : Prop :=
  (∀ Φ : Fin 2 → Bool,
    xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit Φ =
      (1 / 2 : ℝ) *
        xi_poisson_kl_coarsegraining_projection_coefficient_l2_norm_sq
          (xi_poisson_kl_coarsegraining_projection_coefficient_condexp Φ)) ∧
    (∀ Φ : Fin 2 → Bool,
      xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit Φ ≤ 1 / 8) ∧
    (∀ Φ : Fin 2 → Bool,
      xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit Φ = 1 / 8 ↔
        xi_poisson_kl_coarsegraining_projection_coefficient_score_measurable Φ)

/-- Paper label: `thm:xi-poisson-kl-coarsegraining-projection-coefficient`. In the two-point seed
model, the coarsegrained second-order KL coefficient is exactly one half of the squared `L²` norm
of the projected score, contraction gives the universal bound `1/8`, and equality means the score
already factors through the coarsegraining. -/
theorem paper_xi_poisson_kl_coarsegraining_projection_coefficient :
    xi_poisson_kl_coarsegraining_projection_coefficient_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ
    by_cases hΦ : Φ 0 = Φ 1
    · simp [xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit,
        xi_poisson_kl_coarsegraining_projection_coefficient_condexp, hΦ,
        xi_poisson_kl_coarsegraining_projection_coefficient_l2_norm_sq]
    · rw [xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit, dif_neg hΦ]
      rw [xi_poisson_kl_coarsegraining_projection_coefficient_condexp, dif_neg hΦ]
      rw [xi_poisson_kl_coarsegraining_projection_coefficient_score_norm]
      norm_num
  · intro Φ
    by_cases hΦ : Φ 0 = Φ 1
    · simp [xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit, hΦ]
    · simp [xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit, hΦ]
  · intro Φ
    by_cases hΦ : Φ 0 = Φ 1
    · constructor
      · intro hEq
        have : (0 : ℝ) = 1 / 8 := by
          simpa [xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit, hΦ] using hEq
        norm_num at this
      · intro hMeas
        exfalso
        exact
          (xi_poisson_kl_coarsegraining_projection_coefficient_not_measurable_of_eq hΦ) hMeas
    · constructor
      · intro _
        exact xi_poisson_kl_coarsegraining_projection_coefficient_score_measurable_of_ne hΦ
      · intro _
        simp [xi_poisson_kl_coarsegraining_projection_coefficient_kl_limit, hΦ]

end

end Omega.Zeta
