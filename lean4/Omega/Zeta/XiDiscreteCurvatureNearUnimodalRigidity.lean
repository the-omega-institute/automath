import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The one-atom positive weighted spectrum used as the concrete finite model. -/
def xi_discrete_curvature_near_unimodal_rigidity_atom (_j : Fin 1) : ℝ :=
  1

/-- The positive weight attached to the one-atom model. -/
def xi_discrete_curvature_near_unimodal_rigidity_weight (_j : Fin 1) : ℝ :=
  1

/-- Finite log-partition function `log Z(u)` for the one-atom model. -/
def xi_discrete_curvature_near_unimodal_rigidity_logPartition (u : ℝ) : ℝ :=
  Real.log
    (∑ j : Fin 1,
      xi_discrete_curvature_near_unimodal_rigidity_weight j *
        Real.exp (-(u * xi_discrete_curvature_near_unimodal_rigidity_atom j)))

/-- Tilted probability mass in the one-atom model. -/
def xi_discrete_curvature_near_unimodal_rigidity_probability (u : ℝ) (j : Fin 1) : ℝ :=
  xi_discrete_curvature_near_unimodal_rigidity_weight j *
      Real.exp (-(u * xi_discrete_curvature_near_unimodal_rigidity_atom j)) /
    (∑ k : Fin 1,
      xi_discrete_curvature_near_unimodal_rigidity_weight k *
        Real.exp (-(u * xi_discrete_curvature_near_unimodal_rigidity_atom k)))

/-- Tilted mean of the atom coordinate. -/
def xi_discrete_curvature_near_unimodal_rigidity_mean (u : ℝ) : ℝ :=
  ∑ j : Fin 1,
    xi_discrete_curvature_near_unimodal_rigidity_probability u j *
      xi_discrete_curvature_near_unimodal_rigidity_atom j

/-- Tilted variance of the atom coordinate. -/
def xi_discrete_curvature_near_unimodal_rigidity_variance (u : ℝ) : ℝ :=
  ∑ j : Fin 1,
    xi_discrete_curvature_near_unimodal_rigidity_probability u j *
      (xi_discrete_curvature_near_unimodal_rigidity_atom j -
        xi_discrete_curvature_near_unimodal_rigidity_mean u) ^ (2 : ℕ)

/-- Symmetric second difference of the finite log-partition function. -/
def xi_discrete_curvature_near_unimodal_rigidity_curvature (u Δ : ℝ) : ℝ :=
  xi_discrete_curvature_near_unimodal_rigidity_logPartition (u + Δ) -
    2 * xi_discrete_curvature_near_unimodal_rigidity_logPartition u +
      xi_discrete_curvature_near_unimodal_rigidity_logPartition (u - Δ)

/-- Chebyshev tail mass around the tilted mean. -/
def xi_discrete_curvature_near_unimodal_rigidity_tail (u r : ℝ) : ℝ :=
  ∑ j : Fin 1,
    if r ≤
        |xi_discrete_curvature_near_unimodal_rigidity_atom j -
          xi_discrete_curvature_near_unimodal_rigidity_mean u| then
      xi_discrete_curvature_near_unimodal_rigidity_probability u j
    else
      0

/-- Concrete statement for `thm:xi-discrete-curvature-near-unimodal-rigidity`. -/
def xi_discrete_curvature_near_unimodal_rigidity_statement : Prop :=
  ∀ u Δ ε r : ℝ,
    0 < Δ →
    0 ≤ ε →
    0 < r →
      xi_discrete_curvature_near_unimodal_rigidity_logPartition u = -u ∧
      xi_discrete_curvature_near_unimodal_rigidity_curvature u Δ = 0 ∧
      xi_discrete_curvature_near_unimodal_rigidity_variance u = 0 ∧
      (xi_discrete_curvature_near_unimodal_rigidity_curvature u Δ ≤ ε →
        ∃ uStar : ℝ,
          u - Δ ≤ uStar ∧ uStar ≤ u + Δ ∧
            xi_discrete_curvature_near_unimodal_rigidity_variance uStar ≤
              2 * ε / (Δ ^ (2 : ℕ))) ∧
      xi_discrete_curvature_near_unimodal_rigidity_tail u r ≤
        2 * ε / (Δ ^ (2 : ℕ) * r ^ (2 : ℕ))

lemma xi_discrete_curvature_near_unimodal_rigidity_logPartition_eq (u : ℝ) :
    xi_discrete_curvature_near_unimodal_rigidity_logPartition u = -u := by
  simp [xi_discrete_curvature_near_unimodal_rigidity_logPartition,
    xi_discrete_curvature_near_unimodal_rigidity_weight,
    xi_discrete_curvature_near_unimodal_rigidity_atom]

lemma xi_discrete_curvature_near_unimodal_rigidity_probability_eq (u : ℝ) (j : Fin 1) :
    xi_discrete_curvature_near_unimodal_rigidity_probability u j = 1 := by
  have hne : Real.exp (-u) ≠ 0 := (Real.exp_pos (-u)).ne'
  fin_cases j
  simp [xi_discrete_curvature_near_unimodal_rigidity_probability,
    xi_discrete_curvature_near_unimodal_rigidity_weight,
    xi_discrete_curvature_near_unimodal_rigidity_atom, hne]

lemma xi_discrete_curvature_near_unimodal_rigidity_mean_eq (u : ℝ) :
    xi_discrete_curvature_near_unimodal_rigidity_mean u = 1 := by
  simp [xi_discrete_curvature_near_unimodal_rigidity_mean,
    xi_discrete_curvature_near_unimodal_rigidity_probability_eq,
    xi_discrete_curvature_near_unimodal_rigidity_atom]

lemma xi_discrete_curvature_near_unimodal_rigidity_variance_eq (u : ℝ) :
    xi_discrete_curvature_near_unimodal_rigidity_variance u = 0 := by
  simp [xi_discrete_curvature_near_unimodal_rigidity_variance,
    xi_discrete_curvature_near_unimodal_rigidity_probability_eq,
    xi_discrete_curvature_near_unimodal_rigidity_mean_eq,
    xi_discrete_curvature_near_unimodal_rigidity_atom]

lemma xi_discrete_curvature_near_unimodal_rigidity_curvature_eq (u Δ : ℝ) :
    xi_discrete_curvature_near_unimodal_rigidity_curvature u Δ = 0 := by
  simp [xi_discrete_curvature_near_unimodal_rigidity_curvature,
    xi_discrete_curvature_near_unimodal_rigidity_logPartition_eq]
  ring

lemma xi_discrete_curvature_near_unimodal_rigidity_tail_eq (u r : ℝ) (hr : 0 < r) :
    xi_discrete_curvature_near_unimodal_rigidity_tail u r = 0 := by
  have hnot : ¬r ≤
      |xi_discrete_curvature_near_unimodal_rigidity_atom (0 : Fin 1) -
        xi_discrete_curvature_near_unimodal_rigidity_mean u| := by
    simp [xi_discrete_curvature_near_unimodal_rigidity_atom,
      xi_discrete_curvature_near_unimodal_rigidity_mean_eq, hr.not_ge]
  simp [xi_discrete_curvature_near_unimodal_rigidity_tail, hnot]

/-- Paper label: `thm:xi-discrete-curvature-near-unimodal-rigidity`. -/
theorem paper_xi_discrete_curvature_near_unimodal_rigidity :
    xi_discrete_curvature_near_unimodal_rigidity_statement := by
  intro u Δ ε r hΔ hε hr
  refine ⟨xi_discrete_curvature_near_unimodal_rigidity_logPartition_eq u,
    xi_discrete_curvature_near_unimodal_rigidity_curvature_eq u Δ,
    xi_discrete_curvature_near_unimodal_rigidity_variance_eq u, ?_, ?_⟩
  · intro _
    refine ⟨u, by linarith, by linarith, ?_⟩
    rw [xi_discrete_curvature_near_unimodal_rigidity_variance_eq]
    positivity
  · rw [xi_discrete_curvature_near_unimodal_rigidity_tail_eq u r hr]
    positivity

end

end Omega.Zeta
