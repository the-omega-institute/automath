import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_time_part9sa_renyi_spectrum_explicit_bernoulli_experiment
    (renyiLimit renyiBernoulli : ℝ → ℝ)
    (hneq : ∀ α, 0 < α → α ≠ 1 → renyiLimit α = renyiBernoulli α)
    (hkl : renyiLimit 1 = renyiBernoulli 1) :
    ∀ α, 0 < α → renyiLimit α = renyiBernoulli α := by
  intro α hα
  by_cases hα_one : α = 1
  · subst α
    exact hkl
  · exact hneq α hα hα_one

end Omega.Zeta
