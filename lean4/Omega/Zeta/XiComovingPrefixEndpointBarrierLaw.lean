import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The endpoint detection margin from the comoving-prefix model. -/
noncomputable def xiComovingEndpointMargin (Δ δ : ℝ) : ℝ :=
  (4 * δ) / (Δ ^ (2 : ℕ) + (1 + δ) ^ (2 : ℕ))

/-- Worst-case quantization error for `B` prefix bits over `[-T,T]`. -/
noncomputable def xiComovingPrefixError (T : ℝ) (B : ℕ) : ℝ :=
  T * (2 : ℝ) ^ (-(B : ℝ))

/-- The closed-form minimal real endpoint budget. -/
noncomputable def xiComovingPrefixPmin (T δ₀ : ℝ) (B : ℕ) : ℝ :=
  Real.log (((xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ)) / (4 * δ₀)) /
    Real.log 2

/-- Paper label: `thm:xi-comoving-prefix-endpoint-barrier-law`.
The concrete seed isolates the worst-case margin at `δ = δ₀` and `|γ - x₀| = η_B`, then rewrites
the corresponding threshold as a closed `log₂` budget. -/
theorem paper_xi_comoving_prefix_endpoint_barrier_law {T δ₀ : ℝ} {B : ℕ}
    (hδ₀ : 0 < δ₀) (hδ₀_half : δ₀ ≤ 1 / 2) :
    (∀ {δ Δ : ℝ}, δ₀ ≤ δ → δ ≤ 1 / 2 → Δ ^ (2 : ℕ) ≤ (xiComovingPrefixError T B) ^ (2 : ℕ) →
      xiComovingEndpointMargin (xiComovingPrefixError T B) δ₀ ≤ xiComovingEndpointMargin Δ δ) ∧
    xiComovingPrefixPmin T δ₀ B =
      Real.log (((xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ)) / (4 * δ₀)) /
        Real.log 2 := by
  refine ⟨?_, rfl⟩
  intro δ Δ hδ hδ_half hΔ
  have hδpos : 0 < δ := lt_of_lt_of_le hδ₀ hδ
  have hOneδ₀ : 0 < 1 + δ₀ := by linarith
  have hOneδ : 0 < 1 + δ := by linarith
  have hdenLeft : 0 < (xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ) := by
    have : 0 < (1 + δ₀) ^ (2 : ℕ) := by positivity
    positivity
  have hdenRight : 0 < Δ ^ (2 : ℕ) + (1 + δ) ^ (2 : ℕ) := by
    have : 0 < (1 + δ) ^ (2 : ℕ) := by positivity
    positivity
  apply (div_le_div_iff₀ hdenLeft hdenRight).2
  have hbound :
      δ₀ * (Δ ^ (2 : ℕ) + (1 + δ) ^ (2 : ℕ)) ≤
        δ₀ * ((xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ) ^ (2 : ℕ)) := by
    have hδ₀_nonneg : 0 ≤ δ₀ := le_of_lt hδ₀
    gcongr
  have hmono :
      δ₀ * ((xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ) ^ (2 : ℕ)) ≤
        δ * ((xiComovingPrefixError T B) ^ (2 : ℕ) + (1 + δ₀) ^ (2 : ℕ)) := by
    have hηnonneg : 0 ≤ (xiComovingPrefixError T B) ^ (2 : ℕ) := by positivity
    have hδδ₀ : δ * δ₀ ≤ 1 := by
      nlinarith
    have hfac_nonneg : 0 ≤ (δ - δ₀) * ((xiComovingPrefixError T B) ^ (2 : ℕ) + 1 - δ * δ₀) := by
      have hsecond : 0 ≤ (xiComovingPrefixError T B) ^ (2 : ℕ) + 1 - δ * δ₀ := by
        nlinarith
      have hfirst : 0 ≤ δ - δ₀ := by
        linarith
      exact mul_nonneg hfirst hsecond
    nlinarith
  nlinarith

end Omega.Zeta
