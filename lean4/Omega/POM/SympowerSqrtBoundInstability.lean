import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The non-Perron eigenvalue candidate produced by symmetrizing `u^(⊙(b-1)) ⊙ v`. -/
def pom_sympower_sqrt_bound_instability_candidate (ρ μ : ℝ) (b : ℕ) : ℝ :=
  ρ ^ (b - 1) * μ

/-- The square-root barrier for the Perron root `ρ^b`, recorded with the natural exponent `⌊b / 2⌋`.
-/
def pom_sympower_sqrt_bound_instability_sqrt_barrier (ρ : ℝ) (b : ℕ) : ℝ :=
  ρ ^ (b / 2)

/-- Paper label: `thm:pom-sympower-sqrt-bound-instability`.
In the concrete surrogate, once `ρ > 1` and the non-Perron modulus `η = |μ|` is itself `> 1`,
the symmetrized eigenvalue candidate `ρ^(b-1) μ` already beats the square-root barrier from
degree `b0 = 2` onward. -/
theorem paper_pom_sympower_sqrt_bound_instability
    (ρ η μ : ℝ) (hρ : 1 < ρ) (hη : 1 < η) (hμ : |μ| = η) :
    ∃ b0 : ℕ, b0 = 2 ∧ ∀ b ≥ b0,
      |pom_sympower_sqrt_bound_instability_candidate ρ μ b| >
        pom_sympower_sqrt_bound_instability_sqrt_barrier ρ b := by
  refine ⟨2, rfl, ?_⟩
  intro b hb
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  have hpow_nonneg : 0 ≤ ρ ^ (b - 1) := le_of_lt (pow_pos hρpos _)
  have hpow_pos : 0 < ρ ^ (b - 1) := pow_pos hρpos _
  have hdiv : b / 2 ≤ b - 1 := by
    omega
  have hpow_le : ρ ^ (b / 2) ≤ ρ ^ (b - 1) := by
    exact pow_le_pow_right₀ (le_of_lt hρ) hdiv
  have hmul_lt : ρ ^ (b - 1) < ρ ^ (b - 1) * η := by
    simpa using mul_lt_mul_of_pos_left hη hpow_pos
  have hlt : ρ ^ (b / 2) < ρ ^ (b - 1) * η := lt_of_le_of_lt hpow_le hmul_lt
  simpa [pom_sympower_sqrt_bound_instability_candidate,
    pom_sympower_sqrt_bound_instability_sqrt_barrier, abs_mul, abs_of_nonneg hpow_nonneg, hμ] using
    hlt

end Omega.POM
