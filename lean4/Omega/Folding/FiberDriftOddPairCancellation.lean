import Mathlib
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Folding.ResidualPushforwardKernelByFiberProbability

namespace Omega.Folding

open scoped BigOperators

/-- The affine complement involution on the residue side of the single-coordinate model. -/
def fold_fiber_drift_odd_and_pair_cancellation_tau (m : ℕ) :
    ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m) →
      ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m) :=
  fun r => (Nat.fib (m + 1) - 2 : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) - r

/-- The single-coordinate drift extracted from the pushforward kernel. -/
def fold_fiber_drift_odd_and_pair_cancellation_drift (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) : ℚ :=
  foldResidualPushforwardKernel m k r (r + foldFiberSingleCoordinateAffineDifferenceShift m k) -
    foldResidualPushforwardKernel m k r (r - foldFiberSingleCoordinateAffineDifferenceShift m k)

private noncomputable def
    fold_fiber_drift_odd_and_pair_cancellation_profile_equiv_bool (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    {x : foldFiberSingleCoordinateState m // foldFiberSingleCoordinateResidue m k x = r} ≃ Bool where
  toFun x := x.1.2
  invFun b := ⟨(r - if b then foldFiberSingleCoordinateAffineDifferenceShift m k else 0, b), by
    simp [foldFiberSingleCoordinateResidue]⟩
  left_inv x := by
    rcases x with ⟨⟨s, b⟩, hx⟩
    have hs : s = r - if b then foldFiberSingleCoordinateAffineDifferenceShift m k else 0 := by
      simpa [foldFiberSingleCoordinateResidue] using eq_sub_of_add_eq hx
    apply Subtype.ext
    simp [hs]
  right_inv b := by
    simp

private theorem fold_fiber_drift_odd_and_pair_cancellation_profile_eq_two (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    foldFiberSingleCoordinateProfile m k r = 2 := by
  classical
  unfold foldFiberSingleCoordinateProfile
  simpa using
    Fintype.card_congr
      (fold_fiber_drift_odd_and_pair_cancellation_profile_equiv_bool m k r)

private noncomputable def
    fold_fiber_drift_odd_and_pair_cancellation_onecount_equiv_fin_one (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    {x : foldFiberSingleCoordinateState m //
      x.2 = true ∧ foldFiberSingleCoordinateResidue m k x = r} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨(r - foldFiberSingleCoordinateAffineDifferenceShift m k, true), by
    simp [foldFiberSingleCoordinateResidue]⟩
  left_inv x := by
    rcases x with ⟨⟨s, b⟩, hx⟩
    rcases hx with ⟨hb, hr⟩
    have hb' : b = true := by simpa using hb
    subst b
    have hs : s = r - foldFiberSingleCoordinateAffineDifferenceShift m k := by
      simpa [foldFiberSingleCoordinateResidue] using eq_sub_of_add_eq hr
    apply Subtype.ext
    simp [hs]
  right_inv i := by
    fin_cases i
    rfl

private theorem fold_fiber_drift_odd_and_pair_cancellation_onecount_eq_one (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    foldFiberSingleCoordinateOneCount m k r = 1 := by
  classical
  unfold foldFiberSingleCoordinateOneCount
  simpa using
    Fintype.card_congr
      (fold_fiber_drift_odd_and_pair_cancellation_onecount_equiv_fin_one m k r)

private theorem fold_fiber_drift_odd_and_pair_cancellation_fiber_probability_eq_half (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    foldResidualFiberProbability m k r = (1 / 2 : ℚ) := by
  unfold foldResidualFiberProbability
  rw [fold_fiber_drift_odd_and_pair_cancellation_onecount_eq_one,
    fold_fiber_drift_odd_and_pair_cancellation_profile_eq_two]
  norm_num

private theorem fold_fiber_drift_odd_and_pair_cancellation_drift_eq_zero (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    fold_fiber_drift_odd_and_pair_cancellation_drift m k r = 0 := by
  unfold fold_fiber_drift_odd_and_pair_cancellation_drift
  have hKernel := paper_fold_residual_pushforward_kernel_by_fiber_probability m k r
  rw [hKernel.1, hKernel.2,
    fold_fiber_drift_odd_and_pair_cancellation_fiber_probability_eq_half m k r]
  by_cases hm0 : m = 0
  · subst hm0
    norm_num
  · have hmq : (m : ℚ) ≠ 0 := by
      exact_mod_cast hm0
    field_simp [hmq]
    ring

/-- Paper label: `cor:fold-fiber-drift-odd-and-pair-cancellation`.
In the concrete single-coordinate residue model, every fiber probability is exactly `1/2`, so the
pushforward drift is identically zero. The complement involution therefore flips the drift, and
every `τ_m`-invariant weighted sum cancels exactly. -/
theorem paper_fold_fiber_drift_odd_and_pair_cancellation (m k : ℕ) :
    (∀ r,
      foldResidualFiberProbability m k
          (fold_fiber_drift_odd_and_pair_cancellation_tau m r) =
        1 - foldResidualFiberProbability m k r) ∧
      (∀ r,
        fold_fiber_drift_odd_and_pair_cancellation_drift m k
            (fold_fiber_drift_odd_and_pair_cancellation_tau m r) =
          -fold_fiber_drift_odd_and_pair_cancellation_drift m k r) ∧
      (∀ μ f : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m) → ℚ,
        (∀ r, μ (fold_fiber_drift_odd_and_pair_cancellation_tau m r) = μ r) →
        (∀ r, f (fold_fiber_drift_odd_and_pair_cancellation_tau m r) = f r) →
        ∑ r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m),
          μ r * fold_fiber_drift_odd_and_pair_cancellation_drift m k r * f r = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    rw [fold_fiber_drift_odd_and_pair_cancellation_fiber_probability_eq_half,
      fold_fiber_drift_odd_and_pair_cancellation_fiber_probability_eq_half]
    norm_num
  · intro r
    rw [fold_fiber_drift_odd_and_pair_cancellation_drift_eq_zero,
      fold_fiber_drift_odd_and_pair_cancellation_drift_eq_zero]
    ring
  · intro μ f hμ hf
    classical
    simp [fold_fiber_drift_odd_and_pair_cancellation_drift_eq_zero]

end Omega.Folding
