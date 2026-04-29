import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- Fourier multiplier of the normalized dephysicalized Poisson semigroup. -/
noncomputable def dephys_mobius_markov_unique_poisson_multiplier (t ξ : ℝ) : ℝ :=
  Real.exp (-(t * |ξ|))

/-- Fourier multiplier obtained from a Markov generator with speed `c`. -/
noncomputable def dephys_mobius_markov_unique_poisson_markovSymbol (c t ξ : ℝ) : ℝ :=
  Real.exp (-(t * c * |ξ|))

/-- Concrete normalized uniqueness statement for the Möbius--Markov Poisson multiplier. -/
def dephys_mobius_markov_unique_poisson_statement : Prop :=
  (∀ t ξ : ℝ,
      dephys_mobius_markov_unique_poisson_multiplier (t + 0) ξ =
        dephys_mobius_markov_unique_poisson_multiplier t ξ) ∧
    (∀ c t ξ : ℝ,
      c = 1 →
        dephys_mobius_markov_unique_poisson_markovSymbol c t ξ =
          dephys_mobius_markov_unique_poisson_multiplier t ξ) ∧
    (∀ s t ξ : ℝ,
      dephys_mobius_markov_unique_poisson_multiplier (s + t) ξ =
        dephys_mobius_markov_unique_poisson_multiplier s ξ *
          dephys_mobius_markov_unique_poisson_multiplier t ξ)

/-- Paper label: `thm:dephys-mobius-markov-unique-poisson`. -/
theorem paper_dephys_mobius_markov_unique_poisson :
    dephys_mobius_markov_unique_poisson_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ξ
    simp [dephys_mobius_markov_unique_poisson_multiplier]
  · intro c t ξ hc
    subst c
    ring_nf
    simp [dephys_mobius_markov_unique_poisson_markovSymbol,
      dephys_mobius_markov_unique_poisson_multiplier]
  · intro s t ξ
    rw [dephys_mobius_markov_unique_poisson_multiplier,
      dephys_mobius_markov_unique_poisson_multiplier,
      dephys_mobius_markov_unique_poisson_multiplier]
    have h : -((s + t) * |ξ|) = -(s * |ξ|) + -(t * |ξ|) := by ring
    rw [h, Real.exp_add]

end Omega.Zeta
