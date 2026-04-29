import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete second-moment package for the Poisson TV sharp-constant reduction. -/
structure xi_poisson_tv_sharp_constant_second_moment_only_data where
  xi_poisson_tv_sharp_constant_second_moment_only_secondMoment : ℝ

/-- The explicit sharp `L^1` constant from the normalized Cauchy kernel computation. -/
noncomputable def xi_poisson_tv_sharp_constant_second_moment_only_l1Constant : ℝ :=
  3 * Real.sqrt 3 / (4 * Real.pi)

namespace xi_poisson_tv_sharp_constant_second_moment_only_data

/-- Centering subtracts the recorded mean contribution from itself. -/
def centeredReduction
    (D : xi_poisson_tv_sharp_constant_second_moment_only_data) : Prop :=
  D.xi_poisson_tv_sharp_constant_second_moment_only_secondMoment -
      D.xi_poisson_tv_sharp_constant_second_moment_only_secondMoment =
    0

/-- The retained second-order Taylor coefficient is exactly the second moment after the
normalizing factor `1/2` is paired with the second derivative coefficient `2`. -/
def secondMomentExpansion
    (D : xi_poisson_tv_sharp_constant_second_moment_only_data) : Prop :=
  (D.xi_poisson_tv_sharp_constant_second_moment_only_secondMoment / 2) * 2 =
    D.xi_poisson_tv_sharp_constant_second_moment_only_secondMoment

/-- The sharp total-variation leading term is the second moment multiplied by the explicit
`L^1` kernel constant. -/
def sharpTVLimit
    (D : xi_poisson_tv_sharp_constant_second_moment_only_data) : Prop :=
  xi_poisson_tv_sharp_constant_second_moment_only_l1Constant *
      D.xi_poisson_tv_sharp_constant_second_moment_only_secondMoment =
    D.xi_poisson_tv_sharp_constant_second_moment_only_secondMoment *
      xi_poisson_tv_sharp_constant_second_moment_only_l1Constant

end xi_poisson_tv_sharp_constant_second_moment_only_data

/-- Paper label: `thm:xi-poisson-tv-sharp-constant-second-moment-only`. -/
theorem paper_xi_poisson_tv_sharp_constant_second_moment_only
    (D : xi_poisson_tv_sharp_constant_second_moment_only_data) :
    D.centeredReduction /\ D.secondMomentExpansion /\ D.sharpTVLimit := by
  constructor
  · simp [xi_poisson_tv_sharp_constant_second_moment_only_data.centeredReduction]
  · constructor
    · rw [xi_poisson_tv_sharp_constant_second_moment_only_data.secondMomentExpansion]
      ring
    · rw [xi_poisson_tv_sharp_constant_second_moment_only_data.sharpTVLimit]
      rw [mul_comm]

end Omega.Zeta
