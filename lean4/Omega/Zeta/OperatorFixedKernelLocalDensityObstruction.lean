import Mathlib.Topology.Separation.Basic
import Omega.Zeta.CriticalLineGapEntropyRateZero

open Filter
open scoped Topology

namespace Omega.Zeta

/-- A positive constant sequence cannot converge to zero. -/
theorem const_pos_not_tendsto_zero {c : ℝ} (hc : 0 < c) :
    ¬ Tendsto (fun _ : ℕ => c) atTop (𝓝 0) := by
  simpa [hc.ne'] using
    (tendsto_const_nhds_iff (l := atTop) (c := c) (d := (0 : ℝ)))

/-- Paper seed: periodic nearest-neighbor gaps live in a fixed finite set, while a
    cellwise mean gap `Δ / B` stays uniformly positive and therefore cannot shrink to
    zero along height. This rules out a variable-density collapse mechanism.
    prop:operator-fixed-kernel-local-density-obstruction -/
theorem paper_operator_fixed_kernel_local_density_obstruction_seeds
    {B : ℕ} (hB : 0 < B) (g : ℕ → ℝ) (hperiodic : ∀ n, g (n + B) = g n)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ gaps : Finset ℝ,
      (∀ n, g n ∈ gaps) ∧
      let meanGap : ℝ := Δ / (B : ℝ)
      0 < meanGap ∧ ¬ Tendsto (fun _ : ℕ => meanGap) atTop (𝓝 0) := by
  classical
  obtain ⟨block, hblock⟩ :=
    paper_operator_critical_line_gap_entropy_rate_zero_seeds hB g hperiodic
  refine ⟨Finset.univ.image block, ?_, ?_⟩
  · intro n
    rw [hblock n]
    exact Finset.mem_image.mpr ⟨⟨n % B, Nat.mod_lt n hB⟩, by simp⟩
  · dsimp
    have hmean : 0 < Δ / (B : ℝ) := by
      exact div_pos hΔ (show (0 : ℝ) < (B : ℝ) from by exact_mod_cast hB)
    exact ⟨hmean, const_pos_not_tendsto_zero hmean⟩

end Omega.Zeta
