import Mathlib

open Filter Topology

namespace Omega.Conclusion

/-- Total flux error at dyadic refinement level `r`. -/
def dyadicFluxError (flux : ℝ) (S : ℕ → ℝ) (r : ℕ) : ℝ :=
  S r - flux

/-- Level-to-level dyadic flux defect. -/
def dyadicFluxDefect (S : ℕ → ℝ) (r : ℕ) : ℝ :=
  S r - S (r + 1)

/-- The `O(h^3)` small-rectangle estimate summed over one dyadic level. -/
noncomputable def dyadicFluxErrorBudget (m0 : ℕ) (C : ℝ) (r : ℕ) : ℝ :=
  C * (((1 : ℝ) / 8) ^ m0) * (((1 : ℝ) / 2) ^ r)

lemma sum_range_dyadicFluxDefect (S : ℕ → ℝ) (n : ℕ) :
    Finset.sum (Finset.range n) (fun j => dyadicFluxDefect S j) = S 0 - S n := by
  induction n with
  | zero =>
      simp [dyadicFluxDefect]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, dyadicFluxDefect]
      ring

/-- Paper label: `thm:conclusion-nonabelian-dyadic-flux-defect-telescoping`. A geometric levelwise
error bound forces convergence of the refined flux sums, absolute summability of the dyadic defect
series, and the resulting telescoping `HasSum` identity. -/
theorem paper_conclusion_nonabelian_dyadic_flux_defect_telescoping
    (m0 : ℕ) (flux : ℝ) (S : ℕ → ℝ) (C : ℝ)
    (_hC : 0 ≤ C)
    (hbound : ∀ r : ℕ, ‖dyadicFluxError flux S r‖ ≤ dyadicFluxErrorBudget m0 C r) :
    Tendsto S atTop (𝓝 flux) ∧
      Summable (fun r : ℕ => ‖dyadicFluxDefect S r‖) ∧
      HasSum (dyadicFluxDefect S) (S 0 - flux) := by
  have hbudget_tendsto : Tendsto (fun r : ℕ => dyadicFluxErrorBudget m0 C r) atTop (𝓝 0) := by
    have hpow : Tendsto (fun r : ℕ => (((1 : ℝ) / 2) ^ r)) atTop (𝓝 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
    simpa [dyadicFluxErrorBudget, mul_assoc, mul_left_comm, mul_comm] using
      hpow.const_mul (C * (((1 : ℝ) / 8) ^ m0))
  have hS : Tendsto S atTop (𝓝 flux) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun r => norm_nonneg _) ?_ hbudget_tendsto
    intro r
    simpa [dyadicFluxError] using hbound r
  have hbudget_summable : Summable (fun r : ℕ => dyadicFluxErrorBudget m0 C r) := by
    simpa [dyadicFluxErrorBudget, mul_assoc, mul_left_comm, mul_comm] using
      (summable_geometric_two.mul_left (C * (((1 : ℝ) / 8) ^ m0)))
  have hbudget_succ_summable : Summable (fun r : ℕ => dyadicFluxErrorBudget m0 C (r + 1)) := by
    simpa [Function.comp_def] using hbudget_summable.comp_injective Nat.succ_injective
  have hdefect_norm_le :
      ∀ r : ℕ,
        ‖dyadicFluxDefect S r‖ ≤
          dyadicFluxErrorBudget m0 C r + dyadicFluxErrorBudget m0 C (r + 1) := by
    intro r
    dsimp [dyadicFluxDefect, dyadicFluxError]
    calc
      ‖S r - S (r + 1)‖ = ‖(S r - flux) - (S (r + 1) - flux)‖ := by ring_nf
      _ ≤ ‖S r - flux‖ + ‖S (r + 1) - flux‖ := norm_sub_le _ _
      _ ≤ dyadicFluxErrorBudget m0 C r + dyadicFluxErrorBudget m0 C (r + 1) :=
        add_le_add (hbound r) (hbound (r + 1))
  have hdefect_norm_summable : Summable (fun r : ℕ => ‖dyadicFluxDefect S r‖) := by
    refine Summable.of_nonneg_of_le (fun r => norm_nonneg _) hdefect_norm_le ?_
    exact hbudget_summable.add hbudget_succ_summable
  have hpartial :
      Tendsto (fun n : ℕ => Finset.sum (Finset.range n) (fun j => dyadicFluxDefect S j))
        atTop
        (𝓝 (S 0 - flux)) := by
    refine (tendsto_const_nhds.sub hS).congr' ?_
    exact Filter.Eventually.of_forall (fun n => (sum_range_dyadicFluxDefect S n).symm)
  have hhasSum : HasSum (dyadicFluxDefect S) (S 0 - flux) := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm]
    · exact hpartial
    · simpa using hdefect_norm_summable
  exact ⟨hS, hdefect_norm_summable, hhasSum⟩

end Omega.Conclusion
