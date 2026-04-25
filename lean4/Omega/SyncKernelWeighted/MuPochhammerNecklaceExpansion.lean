import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.SyncKernelWeighted.MuPochhammerNecklaceDirichletPolylog

namespace Omega.SyncKernelWeighted

open scoped ArithmeticFunction.Moebius BigOperators

/-- The coefficient `N_n(α)` in the completed `μ`-Pochhammer logarithmic expansion. -/
noncomputable def mu_pochhammer_necklace_expansion_coefficient (α n : ℕ) : ℚ :=
  (muPochhammerNecklaceCoefficient α n : ℚ) / n

/-- Paper label: `prop:mu-pochhammer-necklace-expansion`. The coefficient in the logarithmic
expansion is the divisor-sum Möbius coefficient divided by `n`, and on even lengths it agrees
with the already-packaged necklace correction kernel. -/
theorem paper_mu_pochhammer_necklace_expansion (α : Nat) :
    (∀ n : ℕ, 1 ≤ n →
      mu_pochhammer_necklace_expansion_coefficient α n =
        (∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius d : ℚ) * (α : ℚ) ^ (n / d)) / n) ∧
      (∀ m : ℕ, 1 ≤ m →
        mu_pochhammer_necklace_expansion_coefficient α m =
          (Omega.Zeta.necklaceCorrectionKernel α (2 * m) : ℚ) / m) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    simp [mu_pochhammer_necklace_expansion_coefficient, muPochhammerNecklaceCoefficient]
  · intro m hm
    have hdir := (paper_mu_pochhammer_necklace_dirichlet_polylog α).1 m
    rw [mu_pochhammer_necklace_expansion_coefficient, hdir]

end Omega.SyncKernelWeighted
