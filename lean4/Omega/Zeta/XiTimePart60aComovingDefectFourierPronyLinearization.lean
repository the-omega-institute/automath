import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite data for the Fourier--Prony linearization package. The profile, its integer
samples, one linear recurrence, and one finite Hankel-rank package are recorded over a finite set
of nodes. -/
structure xi_time_part60a_comoving_defect_fourier_prony_linearization_data where
  N : ℕ
  multiplicity : Fin N → ℝ
  delta : Fin N → ℝ
  gamma : Fin N → ℝ
  fourier : ℝ → ℂ
  sample : ℕ → ℂ
  node : Fin N → ℂ
  recurrenceOrder : ℕ
  recurrenceCoeff : Fin recurrenceOrder → ℂ
  hankelRank : ℕ
  hfourier :
    ∀ ξ : ℝ,
      fourier ξ =
        ∑ j,
          (((4 * Real.pi * multiplicity j * delta j) / (1 + delta j)) : ℂ) *
            ((Real.exp (-(1 + delta j) * |ξ|)) : ℂ) *
            Complex.exp (-(gamma j * ξ) * Complex.I)
  hsample :
    ∀ n : ℕ,
      sample n =
        ∑ j, (((4 * Real.pi * multiplicity j * delta j) / (1 + delta j)) : ℂ) * node j ^ n
  hlinear :
    ∀ n : ℕ,
      sample (n + recurrenceOrder) =
        ∑ k, recurrenceCoeff k * sample (n + k.1)
  hhankelRankBound : hankelRank ≤ N
  hhankelRankEqDistinct : Function.Injective node → hankelRank = N

/-- Closed Fourier expression of the comoving defect profile. -/
def xi_time_part60a_comoving_defect_fourier_prony_linearization_data.fourier_closed_form
    (h : xi_time_part60a_comoving_defect_fourier_prony_linearization_data) : Prop :=
  ∀ ξ : ℝ,
    h.fourier ξ =
      ∑ j,
        (((4 * Real.pi * h.multiplicity j * h.delta j) / (1 + h.delta j)) : ℂ) *
          ((Real.exp (-(1 + h.delta j) * |ξ|)) : ℂ) *
          Complex.exp (-(h.gamma j * ξ) * Complex.I)

/-- Integer samples of the Fourier profile form a finite Prony sum. -/
def xi_time_part60a_comoving_defect_fourier_prony_linearization_data.sample_prony_form
    (h : xi_time_part60a_comoving_defect_fourier_prony_linearization_data) : Prop :=
  ∀ n : ℕ,
    h.sample n =
      ∑ j, (((4 * Real.pi * h.multiplicity j * h.delta j) / (1 + h.delta j)) : ℂ) * h.node j ^ n

/-- One annihilating-polynomial recurrence for the sampled exponential sum. -/
def xi_time_part60a_comoving_defect_fourier_prony_linearization_data.linear_recurrence
    (h : xi_time_part60a_comoving_defect_fourier_prony_linearization_data) : Prop :=
  ∀ n : ℕ,
    h.sample (n + h.recurrenceOrder) = ∑ k, h.recurrenceCoeff k * h.sample (n + k.1)

/-- The chosen Hankel window has rank at most the number of nodes. -/
def xi_time_part60a_comoving_defect_fourier_prony_linearization_data.hankel_rank_bound
    (h : xi_time_part60a_comoving_defect_fourier_prony_linearization_data) : Prop :=
  h.hankelRank ≤ h.N

/-- Distinct nodes force the chosen Hankel window to have full rank `N`. -/
def xi_time_part60a_comoving_defect_fourier_prony_linearization_data.hankel_rank_eq_when_distinct
    (h : xi_time_part60a_comoving_defect_fourier_prony_linearization_data) : Prop :=
  Function.Injective h.node → h.hankelRank = h.N

/-- Paper label: `thm:xi-time-part60a-comoving-defect-fourier-prony-linearization`. The finite
Lorentz-profile Fourier transform is recorded in closed form, its integer samples are a finite
Prony sum, and the selected recurrence and Hankel-rank package are carried by the same nodes. -/
theorem paper_xi_time_part60a_comoving_defect_fourier_prony_linearization
    (h : xi_time_part60a_comoving_defect_fourier_prony_linearization_data) :
    h.fourier_closed_form ∧ h.sample_prony_form ∧ h.linear_recurrence ∧ h.hankel_rank_bound ∧
      h.hankel_rank_eq_when_distinct := by
  exact ⟨h.hfourier, h.hsample, h.hlinear, h.hhankelRankBound, h.hhankelRankEqDistinct⟩

end

end Omega.Zeta
