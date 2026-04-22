import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import Omega.Zeta.XiEndpointHeatProbeRstarRegularVariationTail

open Filter
open scoped Topology

namespace Omega.Zeta

/-- Paper label: `thm:xi-endpoint-heat-probe-cyclotomic-complement-radius`.
For the concrete one-atom complement model `t_N = atom * rStar^(N+1)`, the complement support
radius is the supremum of the singleton support and is recovered from the normalized logarithmic
growth rate of the scalar probe sequence. -/
theorem paper_xi_endpoint_heat_probe_cyclotomic_complement_radius
    (rStar atom : ℝ) (hrStar : 0 < rStar) (hatom : 0 < atom) :
    sSup ({x : ℝ | x = rStar}) = rStar ∧
      Tendsto
        (fun N : ℕ =>
          Real.log (xiEndpointHeatProbeAtomicTerm rStar atom (N + 1)) / ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 (Real.log rStar)) := by
  refine ⟨by simp, ?_⟩
  have hEq :
      (fun N : ℕ =>
        Real.log (xiEndpointHeatProbeAtomicTerm rStar atom (N + 1)) / ((N + 1 : ℕ) : ℝ)) =
        fun N : ℕ => Real.log atom / ((N + 1 : ℕ) : ℝ) + Real.log rStar := by
    funext N
    have hpow_pos : 0 < rStar ^ (N + 1) := pow_pos hrStar (N + 1)
    have hden : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    calc
      Real.log (xiEndpointHeatProbeAtomicTerm rStar atom (N + 1)) / ((N + 1 : ℕ) : ℝ)
          = (Real.log atom + Real.log (rStar ^ (N + 1))) / ((N + 1 : ℕ) : ℝ) := by
              rw [xiEndpointHeatProbeAtomicTerm, Real.log_mul hatom.ne' hpow_pos.ne']
      _ = (Real.log atom + ((N + 1 : ℝ) * Real.log rStar)) / ((N + 1 : ℕ) : ℝ) := by
            congr 1
            simpa [Real.rpow_natCast] using Real.log_rpow hrStar (N + 1 : ℝ)
      _ = Real.log atom / ((N + 1 : ℕ) : ℝ) +
            (((N + 1 : ℕ) : ℝ) * Real.log rStar) / ((N + 1 : ℕ) : ℝ) := by
            field_simp [hden]
            rw [Nat.cast_add]
            ring
      _ = Real.log atom / ((N + 1 : ℕ) : ℝ) + Real.log rStar := by
            rw [mul_div_cancel_left₀ _ hden]
  rw [hEq]
  have hzero :
      Tendsto (fun N : ℕ => Real.log atom / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    change Tendsto (((fun n : ℕ => Real.log atom / (n : ℝ)) ∘ fun a : ℕ => a + 1)) atTop (𝓝 0)
    exact (tendsto_const_div_atTop_nhds_zero_nat (Real.log atom)).comp (tendsto_add_atTop_nat 1)
  simpa using hzero.add tendsto_const_nhds

end Omega.Zeta
