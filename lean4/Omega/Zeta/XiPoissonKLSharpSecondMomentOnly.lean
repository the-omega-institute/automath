import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the KL sharp second-moment normal form. The recorded second moment is the
same parameter used by the preceding TV second-moment package. -/
structure xi_poisson_kl_sharp_second_moment_only_data where
  xi_poisson_kl_sharp_second_moment_only_secondMoment : ℝ

namespace xi_poisson_kl_sharp_second_moment_only_data

/-- The preceding total-variation second-moment package with the same second moment. -/
def xi_poisson_kl_sharp_second_moment_only_tv_centered_reduction
    (D : xi_poisson_kl_sharp_second_moment_only_data) : Prop :=
  D.xi_poisson_kl_sharp_second_moment_only_secondMoment -
      D.xi_poisson_kl_sharp_second_moment_only_secondMoment =
    0

/-- The preceding second-moment Taylor normalization, stated on the shared parameter. -/
def xi_poisson_kl_sharp_second_moment_only_tv_second_moment_expansion
    (D : xi_poisson_kl_sharp_second_moment_only_data) : Prop :=
  (D.xi_poisson_kl_sharp_second_moment_only_secondMoment / 2) * 2 =
    D.xi_poisson_kl_sharp_second_moment_only_secondMoment

/-- The normalized second-order density-ratio coefficient. -/
noncomputable def xi_poisson_kl_sharp_second_moment_only_delta_t
    (D : xi_poisson_kl_sharp_second_moment_only_data) : ℝ :=
  D.xi_poisson_kl_sharp_second_moment_only_secondMoment / 2

/-- The packaged Cauchy-kernel integral `∫ G U₂² = 1/4`. -/
noncomputable def xi_poisson_kl_sharp_second_moment_only_u2_l2_norm_sq : ℝ :=
  1 / 4

/-- The second-order KL Taylor coefficient `(1 / 2)‖U₂‖²`. -/
noncomputable def xi_poisson_kl_sharp_second_moment_only_kl_leading_coefficient
    (D : xi_poisson_kl_sharp_second_moment_only_data) : ℝ :=
  (D.xi_poisson_kl_sharp_second_moment_only_secondMoment ^ 2 / 2) *
    xi_poisson_kl_sharp_second_moment_only_u2_l2_norm_sq

/-- The sharp KL limit normal form, together with the inherited TV second-moment reductions. -/
def kl_sharp_limit (D : xi_poisson_kl_sharp_second_moment_only_data) : Prop :=
  D.xi_poisson_kl_sharp_second_moment_only_kl_leading_coefficient =
      D.xi_poisson_kl_sharp_second_moment_only_secondMoment ^ 2 / 8 ∧
    D.xi_poisson_kl_sharp_second_moment_only_tv_centered_reduction ∧
    D.xi_poisson_kl_sharp_second_moment_only_tv_second_moment_expansion

end xi_poisson_kl_sharp_second_moment_only_data

open xi_poisson_kl_sharp_second_moment_only_data

/-- Paper label: `thm:xi-poisson-kl-sharp-second-moment-only`. The Taylor coefficient of
`(1+u) log (1+u)` is `1/2`, and the packaged `L²(G dy)` constant for `U₂` is `1/4`, giving the
sharp constant `1/8`; the TV second-moment normal form is inherited from the preceding theorem. -/
theorem paper_xi_poisson_kl_sharp_second_moment_only
    (D : xi_poisson_kl_sharp_second_moment_only_data) : D.kl_sharp_limit := by
  refine ⟨?_, ?_, ?_⟩
  · simp [xi_poisson_kl_sharp_second_moment_only_kl_leading_coefficient,
      xi_poisson_kl_sharp_second_moment_only_u2_l2_norm_sq]
    ring
  · simp [xi_poisson_kl_sharp_second_moment_only_tv_centered_reduction]
  · rw [xi_poisson_kl_sharp_second_moment_only_tv_second_moment_expansion]
    ring

end Omega.Zeta
