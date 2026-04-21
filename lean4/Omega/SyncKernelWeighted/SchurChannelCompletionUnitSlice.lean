import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.SchurChannelStrictSelfDualFunctoriality
import Omega.SyncKernelWeighted.WeightedCompletionQ

namespace Omega.SyncKernelWeighted

open Matrix

noncomputable section

/-- The unit-slice completion polynomial obtained from the invariant coordinate `S = r + r⁻¹`
after specializing to `r = 1`, hence `S = 2`. -/
def schurChannelCompletionUnitSlice (y : ℝ) : ℝ :=
  weightedCompletionQ 2 y

/-- The Sturm-chain reduction used on the unit slice: root location is reduced to the vanishing of
the completed polynomial in the invariant coordinate. -/
def schurChannelUnitSliceSturmReduction (y : ℝ) : Prop :=
  schurChannelCompletionUnitSlice y = 0

/-- Paper label: `cor:sync-kernel-schur-channel-completion-unit-slice`.

Specializing the strict Schur self-duality theorem to `u = 1 = 1^2` gives the unit-slice channel
functional equation. On the completion side, the invariant Laurent polynomial descends to
`weightedCompletionQ (r + r⁻¹) y`; at `r = 1` this is exactly the unit-slice polynomial
`weightedCompletionQ 2 y`, so vanishing of the original sextic is equivalent to the root-location
problem for this one-variable completed polynomial. -/
theorem paper_sync_kernel_schur_channel_completion_unit_slice {n : Type*} [Fintype n]
    [DecidableEq n] (q : ℕ) (z : ℂ) (B Buinv P : Matrix n n ℂ) (hP : IsUnit P.det)
    (hsim : schurSimilarityLaw q (1 : ℂ) 1 B Buinv P) (y : ℝ) :
    schurSimilarityLaw q (1 : ℂ) 1 B Buinv P ∧
      schurDeterminantFunctionalEquation q (1 : ℂ) 1 z B Buinv ∧
      weightedCompletionLaurent 1 y = schurChannelCompletionUnitSlice y ∧
      (weightedCompletionSextic y 1 = 0 ↔ schurChannelUnitSliceSturmReduction y) ∧
      (schurChannelUnitSliceSturmReduction y ↔ schurChannelCompletionUnitSlice y = 0) := by
  have hdual :=
    paper_sync_kernel_schur_channel_strict_self_dual_functoriality
      (n := n) (q := q) (u := 1) (z := z) B Buinv P hP hsim
  rcases hdual with ⟨hsim', hdet⟩
  have hLaurentQ : weightedCompletionLaurent 1 y = weightedCompletionQ (1 + 1) y := by
    simpa using weightedCompletionLaurent_eq_Q 1 y one_ne_zero
  have hzero : weightedCompletionSextic y 1 = 0 ↔ weightedCompletionQ (1 + 1) y = 0 := by
    simpa using weightedCompletion_eq_zero_iff 1 y one_ne_zero
  have htwo : (1 + 1 : ℝ) = 2 := by norm_num
  refine ⟨hsim', hdet, ?_, ?_, Iff.rfl⟩
  · calc
      weightedCompletionLaurent 1 y = weightedCompletionQ (1 + 1) y := hLaurentQ
      _ = schurChannelCompletionUnitSlice y := by
            rw [htwo, schurChannelCompletionUnitSlice]
  · have hzero' : weightedCompletionSextic y 1 = 0 ↔ weightedCompletionQ 2 y = 0 := by
      rw [htwo] at hzero
      exact hzero
    simpa [schurChannelCompletionUnitSlice, schurChannelUnitSliceSturmReduction] using hzero'

end

end Omega.SyncKernelWeighted
