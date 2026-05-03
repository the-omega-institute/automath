import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:dephys-idempotent-monad-entropy-axiomatic-uniqueness`. -/
theorem paper_dephys_idempotent_monad_entropy_axiomatic_uniqueness {State : Type}
    (Pi : State → State) (RelEnt : State → State → ℝ) (Cost : State → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hPi : ∀ ρ, Pi (Pi ρ) = Pi ρ)
    (hself : ∀ ρ, RelEnt (Pi ρ) (Pi ρ) = 0)
    (hPyth : ∀ ρ σ, Pi σ = σ →
      RelEnt ρ σ = c⁻¹ * Cost ρ + RelEnt (Pi ρ) σ) :
    ∀ ρ, Cost ρ = c * RelEnt ρ (Pi ρ) := by
  intro ρ
  have hpyth := hPyth ρ (Pi ρ) (hPi ρ)
  have hrel : RelEnt ρ (Pi ρ) = c⁻¹ * Cost ρ := by
    simpa [hself ρ] using hpyth
  calc
    Cost ρ = c * (c⁻¹ * Cost ρ) := by
      field_simp [hc]
    _ = c * RelEnt ρ (Pi ρ) := by
      rw [← hrel]

end Omega.Zeta
