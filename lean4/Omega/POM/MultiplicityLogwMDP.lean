import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Quadratic cumulant generating function for the logarithmic-weight moderate-deviation scale. -/
def pom_multiplicity_logw_mdp_quadratic_cgf (sigmaStarSq theta : ℝ) : ℝ :=
  sigmaStarSq * theta ^ (2 : ℕ) / 2

/-- The quadratic rate function produced by the local Gartner--Ellis expansion. -/
def pom_multiplicity_logw_mdp_quadratic_rate (sigmaStarSq x : ℝ) : ℝ :=
  x ^ (2 : ℕ) / (2 * sigmaStarSq)

/-- Right-tail MDP algebra: the optimizing tilt `x / sigmaStarSq` gives the quadratic rate. -/
def pom_multiplicity_logw_mdp_right_tail (sigmaStarSq : ℝ) : Prop :=
  ∀ x : ℝ,
    0 ≤ x →
      0 ≤ pom_multiplicity_logw_mdp_quadratic_rate sigmaStarSq x ∧
        x * (x / sigmaStarSq) -
            pom_multiplicity_logw_mdp_quadratic_cgf sigmaStarSq (x / sigmaStarSq) =
          pom_multiplicity_logw_mdp_quadratic_rate sigmaStarSq x

/-- Left-tail MDP algebra: the optimizing tilt `-x / sigmaStarSq` gives the same rate. -/
def pom_multiplicity_logw_mdp_left_tail (sigmaStarSq : ℝ) : Prop :=
  ∀ x : ℝ,
    0 ≤ x →
      0 ≤ pom_multiplicity_logw_mdp_quadratic_rate sigmaStarSq x ∧
        (-x) * ((-x) / sigmaStarSq) -
            pom_multiplicity_logw_mdp_quadratic_cgf sigmaStarSq ((-x) / sigmaStarSq) =
          pom_multiplicity_logw_mdp_quadratic_rate sigmaStarSq x

/-- Paper label: `prop:pom-multiplicity-logw-mdp`.

For a positive variance constant, the quadratic cumulant expansion gives the same
Gartner--Ellis rate on the right and left moderate-deviation tails. -/
theorem paper_pom_multiplicity_logw_mdp (sigmaStarSq : ℝ) (hSigma : 0 < sigmaStarSq) :
    pom_multiplicity_logw_mdp_right_tail sigmaStarSq ∧
      pom_multiplicity_logw_mdp_left_tail sigmaStarSq := by
  have hSigma_ne : sigmaStarSq ≠ 0 := ne_of_gt hSigma
  constructor
  · intro x _hx
    have hnonneg : 0 ≤ pom_multiplicity_logw_mdp_quadratic_rate sigmaStarSq x := by
      unfold pom_multiplicity_logw_mdp_quadratic_rate
      positivity
    refine ⟨hnonneg, ?_⟩
    unfold pom_multiplicity_logw_mdp_quadratic_cgf
      pom_multiplicity_logw_mdp_quadratic_rate
    field_simp [hSigma_ne]
    ring
  · intro x _hx
    have hnonneg : 0 ≤ pom_multiplicity_logw_mdp_quadratic_rate sigmaStarSq x := by
      unfold pom_multiplicity_logw_mdp_quadratic_rate
      positivity
    refine ⟨hnonneg, ?_⟩
    unfold pom_multiplicity_logw_mdp_quadratic_cgf
      pom_multiplicity_logw_mdp_quadratic_rate
    field_simp [hSigma_ne]
    ring

end

end Omega.POM
