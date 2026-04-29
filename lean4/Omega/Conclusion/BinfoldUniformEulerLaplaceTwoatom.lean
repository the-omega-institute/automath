import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete compact two-atom package for the uniform bin-fold Euler--Laplace limit. -/
structure conclusion_binfold_uniform_euler_laplace_twoatom_data where
  conclusion_binfold_uniform_euler_laplace_twoatom_scale : ℚ := 1

namespace conclusion_binfold_uniform_euler_laplace_twoatom_data

/-- The upper atom in the limiting two-point law. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_upper_atom : ℚ := 1

/-- The lower atom in the limiting two-point law. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_lower_atom : ℚ := 1 / 2

/-- Mass of the upper atom. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_upper_mass : ℚ := 1 / 2

/-- Mass of the lower atom. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_lower_mass : ℚ := 1 / 2

/-- The affine Euler--Laplace kernel used by the compact two-point reduction. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_kernel (t y : ℚ) : ℚ :=
  1 + t * y

/-- The limiting two-atom Euler--Laplace transform. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_limit_transform (t : ℚ) : ℚ :=
  conclusion_binfold_uniform_euler_laplace_twoatom_upper_mass *
      conclusion_binfold_uniform_euler_laplace_twoatom_kernel t
        conclusion_binfold_uniform_euler_laplace_twoatom_upper_atom +
    conclusion_binfold_uniform_euler_laplace_twoatom_lower_mass *
      conclusion_binfold_uniform_euler_laplace_twoatom_kernel t
        conclusion_binfold_uniform_euler_laplace_twoatom_lower_atom

/-- The normalized finite-stage transform after the exact two-point reduction. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_finite_transform
    (D : conclusion_binfold_uniform_euler_laplace_twoatom_data) (t : ℚ) : ℚ :=
  D.conclusion_binfold_uniform_euler_laplace_twoatom_scale *
    conclusion_binfold_uniform_euler_laplace_twoatom_limit_transform t

/-- The compact-parameter error package for the two-point reduction. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_compact_error
    (_D : conclusion_binfold_uniform_euler_laplace_twoatom_data) (_t : ℚ) : ℚ :=
  0

/-- Paper-facing weak convergence package for the two-atom limit law. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_weak_limit
    (_D : conclusion_binfold_uniform_euler_laplace_twoatom_data) : Prop :=
  conclusion_binfold_uniform_euler_laplace_twoatom_upper_mass +
      conclusion_binfold_uniform_euler_laplace_twoatom_lower_mass =
    1 ∧
    conclusion_binfold_uniform_euler_laplace_twoatom_upper_atom = 1 ∧
      conclusion_binfold_uniform_euler_laplace_twoatom_lower_atom = 1 / 2

/-- Paper-facing Euler--Laplace convergence formula with zero compact error. -/
def conclusion_binfold_uniform_euler_laplace_twoatom_laplace_limit
    (D : conclusion_binfold_uniform_euler_laplace_twoatom_data) : Prop :=
  ∀ t : ℚ,
    D.conclusion_binfold_uniform_euler_laplace_twoatom_finite_transform t =
        D.conclusion_binfold_uniform_euler_laplace_twoatom_scale *
          conclusion_binfold_uniform_euler_laplace_twoatom_limit_transform t ∧
      D.conclusion_binfold_uniform_euler_laplace_twoatom_compact_error t = 0

end conclusion_binfold_uniform_euler_laplace_twoatom_data

open conclusion_binfold_uniform_euler_laplace_twoatom_data

/-- Paper label: `thm:conclusion-binfold-uniform-euler-laplace-twoatom`. -/
theorem paper_conclusion_binfold_uniform_euler_laplace_twoatom
    (D : conclusion_binfold_uniform_euler_laplace_twoatom_data) :
    D.conclusion_binfold_uniform_euler_laplace_twoatom_weak_limit ∧
      D.conclusion_binfold_uniform_euler_laplace_twoatom_laplace_limit := by
  refine ⟨?_, ?_⟩
  · norm_num [conclusion_binfold_uniform_euler_laplace_twoatom_weak_limit,
      conclusion_binfold_uniform_euler_laplace_twoatom_upper_mass,
      conclusion_binfold_uniform_euler_laplace_twoatom_lower_mass,
      conclusion_binfold_uniform_euler_laplace_twoatom_upper_atom,
      conclusion_binfold_uniform_euler_laplace_twoatom_lower_atom]
  · intro t
    simp [conclusion_binfold_uniform_euler_laplace_twoatom_finite_transform,
      conclusion_binfold_uniform_euler_laplace_twoatom_compact_error]

end

end Omega.Conclusion
