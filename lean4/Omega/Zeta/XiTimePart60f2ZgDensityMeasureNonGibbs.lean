import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete zero-prefix mass data for the non-Gibbs argument. The three obstruction fields encode
the trichotomy for the pressure gap: exponential growth, constant scale, and exponential decay are
all incompatible with the supplied zero-prefix asymptotics. -/
structure xi_time_part60f2_zg_density_measure_non_gibbs_data where
  zeroPrefixMass : ℕ → ℝ
  zeroPrefix_below_constant_scale :
    ∀ C : ℝ, 1 ≤ C → ∃ n : ℕ, zeroPrefixMass n < C⁻¹
  zeroPrefix_not_exponential_decay :
    ∀ C δ : ℝ, 0 < C → 0 < δ → ∃ n : ℕ, C * Real.exp (-δ * (n : ℝ)) < zeroPrefixMass n
  zeroPrefix_not_exponential_growth :
    ∀ C δ : ℝ,
      1 ≤ C → δ < 0 → ∃ n : ℕ, zeroPrefixMass n < C⁻¹ * Real.exp (-δ * (n : ℝ))

/-- A Gibbs cylinder bound along the zero fixed prefix: for some constant `C ≥ 1` and pressure gap
`δ`, the zero-prefix masses are two-sided comparable to `exp (-δ n)`. -/
def xi_time_part60f2_zg_density_measure_non_gibbs_is_gibbs
    (D : xi_time_part60f2_zg_density_measure_non_gibbs_data) : Prop :=
  ∃ C δ : ℝ,
    1 ≤ C ∧
      ∀ n : ℕ,
        C⁻¹ * Real.exp (-δ * (n : ℝ)) ≤ D.zeroPrefixMass n ∧
          D.zeroPrefixMass n ≤ C * Real.exp (-δ * (n : ℝ))

/-- Target-prefixed contradiction proof: a Gibbs bound forces constant, growing, or exponentially
decaying zero-prefix mass according to the sign of the pressure gap, contradicting the supplied
subexponential zero-prefix asymptotics.
    thm:xi-time-part60f2-zg-density-measure-non-gibbs -/
theorem paper_xi_time_part60f2_zg_density_measure_non_gibbs
    (zeroPrefixMass : ℕ → ℝ)
    (zeroPrefix_below_constant_scale :
      ∀ C : ℝ, 1 ≤ C → ∃ n : ℕ, zeroPrefixMass n < C⁻¹)
    (zeroPrefix_not_exponential_decay :
      ∀ C δ : ℝ, 0 < C → 0 < δ → ∃ n : ℕ, C * Real.exp (-δ * (n : ℝ)) <
        zeroPrefixMass n)
    (zeroPrefix_not_exponential_growth :
      ∀ C δ : ℝ,
        1 ≤ C → δ < 0 → ∃ n : ℕ, zeroPrefixMass n < C⁻¹ * Real.exp (-δ * (n : ℝ))) :
    ¬ xi_time_part60f2_zg_density_measure_non_gibbs_is_gibbs
      { zeroPrefixMass := zeroPrefixMass
        zeroPrefix_below_constant_scale := zeroPrefix_below_constant_scale
        zeroPrefix_not_exponential_decay := zeroPrefix_not_exponential_decay
        zeroPrefix_not_exponential_growth := zeroPrefix_not_exponential_growth } := by
  rintro ⟨C, δ, hC, hGibbs⟩
  by_cases hneg : δ < 0
  · rcases zeroPrefix_not_exponential_growth C δ hC hneg with ⟨n, hn⟩
    have hlower := (hGibbs n).1
    linarith
  · have hδ_nonneg : 0 ≤ δ := le_of_not_gt hneg
    by_cases hzero : δ = 0
    · rcases zeroPrefix_below_constant_scale C hC with ⟨n, hn⟩
      have hlower := (hGibbs n).1
      rw [hzero] at hlower
      simp at hlower
      linarith
    · have hpos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hzero)
      have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
      rcases zeroPrefix_not_exponential_decay C δ hCpos hpos with ⟨n, hn⟩
      have hupper := (hGibbs n).2
      linarith

end Omega.Zeta
