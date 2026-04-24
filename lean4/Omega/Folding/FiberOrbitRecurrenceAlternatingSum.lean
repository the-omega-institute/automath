import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Folding.FiberSingleCoordinateAffineDifference

namespace Omega.Folding

open scoped BigOperators

private noncomputable def foldFiberSingleCoordinateProfileEquivBool' (m k : ℕ)
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

private theorem foldFiberSingleCoordinateProfile_eq_two' (m k : ℕ)
    (r : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) :
    foldFiberSingleCoordinateProfile m k r = 2 := by
  classical
  unfold foldFiberSingleCoordinateProfile
  simpa using Fintype.card_congr (foldFiberSingleCoordinateProfileEquivBool' m k r)

private theorem alternating_range_two_mul_even (n : ℕ) :
    Finset.sum (Finset.range (2 * n)) (fun j => (-1 : ℤ) ^ j * 2) = 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpow_even : (-1 : ℤ) ^ (2 * n) = 1 := by
        rw [pow_mul]
        norm_num
      have hpow_odd : (-1 : ℤ) ^ (2 * n + 1) = -1 := by
        rw [pow_succ, hpow_even]
        norm_num
      rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      simp [ih, hpow_even, hpow_odd]

/-- Paper label: `cor:fold-fiber-orbit-recurrence-alternating-sum`. -/
theorem paper_fold_fiber_orbit_recurrence_alternating_sum
    (m k L : ℕ) (r0 : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m))
    (hperiod :
      (L : ZMod (foldFiberSingleCoordinateAffineDifferenceModulus m)) *
        foldFiberSingleCoordinateAffineDifferenceShift m k = 0) :
    Even L →
      ∑ j : Fin L,
          (-1 : ℤ) ^ j.1 *
            (foldFiberSingleCoordinateProfile m k
              (r0 + (j.1 : ℕ) * foldFiberSingleCoordinateAffineDifferenceShift m k) : ℤ) =
        0 := by
  let _ := hperiod
  intro hEven
  rcases hEven with ⟨n, rfl⟩
  have hconst :
      (∑ j : Fin (n + n),
          (-1 : ℤ) ^ j.1 *
            (foldFiberSingleCoordinateProfile m k
              (r0 + (j.1 : ℕ) * foldFiberSingleCoordinateAffineDifferenceShift m k) : ℤ)) =
        ∑ j : Fin (n + n), (-1 : ℤ) ^ j.1 * 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [foldFiberSingleCoordinateProfile_eq_two']
  calc
    (∑ j : Fin (n + n),
        (-1 : ℤ) ^ j.1 *
          (foldFiberSingleCoordinateProfile m k
            (r0 + (j.1 : ℕ) * foldFiberSingleCoordinateAffineDifferenceShift m k) : ℤ)) =
      ∑ j : Fin (n + n), (-1 : ℤ) ^ j.1 * 2 := hconst
    _ = 0 := by
      rw [Fin.sum_univ_eq_sum_range (f := fun j : ℕ => (-1 : ℤ) ^ j * 2)]
      simpa [two_mul] using alternating_range_two_mul_even n

end Omega.Folding
