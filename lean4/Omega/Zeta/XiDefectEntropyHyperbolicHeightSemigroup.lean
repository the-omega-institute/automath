import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The defect coordinate normalized by the hyperbolic height parameter. -/
noncomputable def xi_defect_entropy_hyperbolic_height_semigroup_delta (s : ℝ) : ℝ :=
  Real.exp s - 1

/-- Weighted height of a finite hyperbolic block. -/
noncomputable def xi_defect_entropy_hyperbolic_height_semigroup_weighted_height {n : ℕ}
    (weights heights : Fin n → ℝ) : ℝ :=
  ∑ i, weights i * heights i

/-- The top-length count of a finite height block. -/
noncomputable def xi_defect_entropy_hyperbolic_height_semigroup_top_length_value
    (n : ℕ) : ℝ :=
  ∑ _i : Fin n, (1 : ℝ)

/-- Uniform translation of every height coordinate. -/
def xi_defect_entropy_hyperbolic_height_semigroup_shift {n : ℕ} (a : ℝ)
    (heights : Fin n → ℝ) : Fin n → ℝ :=
  fun i => heights i + a

/-- Linearization of the defect coordinate: `1 + δ = exp s`. -/
def xi_defect_entropy_hyperbolic_height_semigroup_linearization : Prop :=
  ∀ s : ℝ, 1 + xi_defect_entropy_hyperbolic_height_semigroup_delta s = Real.exp s

/-- The top-length identity for finite height blocks. -/
def xi_defect_entropy_hyperbolic_height_semigroup_top_length : Prop :=
  ∀ n : ℕ, xi_defect_entropy_hyperbolic_height_semigroup_top_length_value n = n

/-- Uniform height shifts form an additive semigroup action. -/
def xi_defect_entropy_hyperbolic_height_semigroup_shift_law : Prop :=
  ∀ {n : ℕ} (a b : ℝ) (heights : Fin n → ℝ),
    xi_defect_entropy_hyperbolic_height_semigroup_shift a
        (xi_defect_entropy_hyperbolic_height_semigroup_shift b heights) =
      xi_defect_entropy_hyperbolic_height_semigroup_shift (a + b) heights

/-- Paper label: `prop:xi-defect-entropy-hyperbolic-height-semigroup`. -/
theorem paper_xi_defect_entropy_hyperbolic_height_semigroup :
    xi_defect_entropy_hyperbolic_height_semigroup_linearization ∧
      xi_defect_entropy_hyperbolic_height_semigroup_top_length ∧
      xi_defect_entropy_hyperbolic_height_semigroup_shift_law := by
  constructor
  · intro s
    simp [xi_defect_entropy_hyperbolic_height_semigroup_delta]
  constructor
  · intro n
    simp [xi_defect_entropy_hyperbolic_height_semigroup_top_length_value]
  · intro n a b heights
    funext i
    simp [xi_defect_entropy_hyperbolic_height_semigroup_shift]
    ring

end Omega.Zeta
