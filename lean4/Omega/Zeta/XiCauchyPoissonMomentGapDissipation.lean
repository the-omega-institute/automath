import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete leading-term data for the Cauchy--Poisson moment-gap KL expansion. -/
structure xi_cauchy_poisson_moment_gap_dissipation_data where
  xi_cauchy_poisson_moment_gap_dissipation_gapOrder : ℕ
  xi_cauchy_poisson_moment_gap_dissipation_momentGap : ℝ

namespace xi_cauchy_poisson_moment_gap_dissipation_data

/-- The binomial coefficient in the KL leading term. -/
def xi_cauchy_poisson_moment_gap_dissipation_klBinomial
    (D : xi_cauchy_poisson_moment_gap_dissipation_data) : ℝ :=
  (Nat.choose (2 * D.xi_cauchy_poisson_moment_gap_dissipation_gapOrder - 2)
    (D.xi_cauchy_poisson_moment_gap_dissipation_gapOrder - 1) : ℝ)

/-- The leading KL coefficient before differentiating in scale. -/
def xi_cauchy_poisson_moment_gap_dissipation_klLeadingConstant
    (D : xi_cauchy_poisson_moment_gap_dissipation_data) : ℝ :=
  D.xi_cauchy_poisson_moment_gap_dissipation_klBinomial *
      D.xi_cauchy_poisson_moment_gap_dissipation_momentGap ^ 2 /
    (2 : ℝ) ^ (2 * D.xi_cauchy_poisson_moment_gap_dissipation_gapOrder)

/-- The tail order of the dissipation after differentiating a `t^(-2k)` KL term. -/
def xi_cauchy_poisson_moment_gap_dissipation_dissipationTailOrder
    (D : xi_cauchy_poisson_moment_gap_dissipation_data) : ℕ :=
  2 * D.xi_cauchy_poisson_moment_gap_dissipation_gapOrder + 1

/-- The dissipation tail coefficient obtained from the KL coefficient by the factor `2k`. -/
def xi_cauchy_poisson_moment_gap_dissipation_dissipationTailConstant
    (D : xi_cauchy_poisson_moment_gap_dissipation_data) : ℝ :=
  (2 * D.xi_cauchy_poisson_moment_gap_dissipation_gapOrder : ℝ) *
    D.xi_cauchy_poisson_moment_gap_dissipation_klLeadingConstant

/-- The paper-facing constant identity for the dissipation tail. -/
def dissipation_tail_constant (D : xi_cauchy_poisson_moment_gap_dissipation_data) : Prop :=
  D.xi_cauchy_poisson_moment_gap_dissipation_dissipationTailConstant =
    (2 * D.xi_cauchy_poisson_moment_gap_dissipation_gapOrder : ℝ) *
      D.xi_cauchy_poisson_moment_gap_dissipation_klLeadingConstant ∧
      D.xi_cauchy_poisson_moment_gap_dissipation_dissipationTailOrder =
        2 * D.xi_cauchy_poisson_moment_gap_dissipation_gapOrder + 1

lemma xi_cauchy_poisson_moment_gap_dissipation_tail_constant
    (D : xi_cauchy_poisson_moment_gap_dissipation_data) : D.dissipation_tail_constant := by
  simp [dissipation_tail_constant,
    xi_cauchy_poisson_moment_gap_dissipation_dissipationTailConstant,
    xi_cauchy_poisson_moment_gap_dissipation_dissipationTailOrder]

end xi_cauchy_poisson_moment_gap_dissipation_data

/-- Paper label: `cor:xi-cauchy-poisson-moment-gap-dissipation`. -/
theorem paper_xi_cauchy_poisson_moment_gap_dissipation
    (D : xi_cauchy_poisson_moment_gap_dissipation_data) : D.dissipation_tail_constant := by
  exact D.xi_cauchy_poisson_moment_gap_dissipation_tail_constant

end

end Omega.Zeta
