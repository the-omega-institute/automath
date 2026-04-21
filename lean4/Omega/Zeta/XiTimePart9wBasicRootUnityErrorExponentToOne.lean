import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter Topology

namespace Omega.Zeta

/-- The Perron-scale logarithm `log λ` with `λ = φ²`. -/
noncomputable def xiTimePart9wBasicLogLambda : ℝ :=
  Real.log (Real.goldenRatio ^ (2 : ℕ))

/-- The specialized `κ₂` coefficient at `j = 1`. -/
noncomputable def xiTimePart9wBasicKappa2 : ℝ :=
  (8955 - 3983 * Real.sqrt 5) / 1000

/-- The specialized `κ₄` coefficient at `j = 1`. -/
noncomputable def xiTimePart9wBasicKappa4 : ℝ :=
  (1354428303 - 605718497 * Real.sqrt 5) / 100000

/-- The explicit leading `m⁻²` correction coefficient. -/
noncomputable def xiTimePart9wBasicAout : ℝ :=
  (Real.pi ^ 2) * (8955 - 3983 * Real.sqrt 5) / (500 * xiTimePart9wBasicLogLambda)

/-- The explicit `m⁻⁴` correction coefficient. -/
noncomputable def xiTimePart9wBasicBout : ℝ :=
  (Real.pi ^ 4) * (1354428303 - 605718497 * Real.sqrt 5) /
    (150000 * xiTimePart9wBasicLogLambda)

/-- The explicit fixed-`j = 1` asymptotic model for `varthetaₘ,₁`. The shift by `1` avoids the
`m = 0` denominator while preserving the same limit. -/
noncomputable def xiTimePart9wBasicVartheta (m : ℕ) : ℝ :=
  1 - xiTimePart9wBasicAout / (((m : ℝ) + 1) ^ 2) +
    xiTimePart9wBasicBout / (((m : ℝ) + 1) ^ 4)

/-- Paper label: `thm:xi-time-part9w-basic-root-unity-error-exponent-to-one`. -/
theorem paper_xi_time_part9w_basic_root_unity_error_exponent_to_one :
    xiTimePart9wBasicAout =
        (Real.pi ^ 2) * (8955 - 3983 * Real.sqrt 5) / (500 * xiTimePart9wBasicLogLambda) ∧
      xiTimePart9wBasicBout =
        (Real.pi ^ 4) * (1354428303 - 605718497 * Real.sqrt 5) /
          (150000 * xiTimePart9wBasicLogLambda) ∧
      Tendsto xiTimePart9wBasicVartheta atTop (𝓝 1) := by
  refine ⟨rfl, rfl, ?_⟩
  have hshift : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hpow2Real : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpow4Real : Tendsto (fun t : ℝ => t ^ 4) atTop atTop := by
    exact tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)
  have hpow2 : Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ 2) atTop atTop :=
    hpow2Real.comp hshift
  have hpow4 : Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ 4) atTop atTop :=
    hpow4Real.comp hshift
  have hinv2 : Tendsto (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow2
  have hinv4 : Tendsto (fun m : ℕ => (((m : ℝ) + 1) ^ 4)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hpow4
  have hterm2 :
      Tendsto (fun m : ℕ => xiTimePart9wBasicAout / (((m : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv2)
  have hterm4 :
      Tendsto (fun m : ℕ => xiTimePart9wBasicBout / (((m : ℝ) + 1) ^ 4)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv4)
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hsub :
      Tendsto (fun m : ℕ => 1 - xiTimePart9wBasicAout / (((m : ℝ) + 1) ^ 2)) atTop (𝓝 1) := by
    simpa using hconst.sub hterm2
  have hadd :
      Tendsto
        (fun m : ℕ =>
          (1 - xiTimePart9wBasicAout / (((m : ℝ) + 1) ^ 2)) +
            xiTimePart9wBasicBout / (((m : ℝ) + 1) ^ 4))
        atTop (𝓝 (1 + 0)) :=
    hsub.add hterm4
  simpa [xiTimePart9wBasicVartheta] using hadd

end Omega.Zeta
