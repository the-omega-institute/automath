import Mathlib
import Mathlib.Data.Finset.SymmDiff
import Omega.Conclusion.BoundaryGodelDistanceDiscreteIsoperimetricLaw

namespace Omega.Conclusion

open scoped symmDiff

/-- Paper label: `cor:conclusion-single-cube-edit-rigidity`.

The lower bound from the discrete isoperimetric law rules out any nonzero symmetric difference
when the boundary distance is strictly smaller than `2n`. In ambient dimension at least `2`, the
sharp case `Dist = 2n` forces the symmetric difference to contain exactly one dyadic cube. -/
theorem paper_conclusion_single_cube_edit_rigidity
    (h : Omega.SPG.DyadicPolyclubeDiscreteIsoperimetryData) (U V : Finset ℕ) (Dist : ℕ)
    (hAmbient : 2 ≤ h.n) (hDist : Dist = h.F) (hDelta : (U ∆ V).card = h.N) :
    (Dist < 2 * h.n → U = V) ∧
      (U ≠ V → Dist = 2 * h.n → (U ∆ V).card = 1) := by
  let NDelta : ℕ := (U ∆ V).card
  have hIso :=
    paper_conclusion_boundary_godel_distance_discrete_isoperimetric_law h Dist NDelta hDist (by
      simpa [NDelta] using hDelta)
  rcases hIso with ⟨hLower, hUpper⟩
  constructor
  · intro hlt
    by_contra hne
    have hNpos : 1 ≤ NDelta := by
      have hneNonempty : (U ∆ V).Nonempty := by
        exact (Finset.symmDiff_nonempty).2 hne
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr hneNonempty)
    have hpow_ge_one : 1 ≤ NDelta ^ (h.n - 1) := by
      exact one_le_pow_of_one_le' hNpos _
    have hbase_le : (2 * h.n) ^ h.n ≤ Dist ^ h.n := by
      calc
        (2 * h.n) ^ h.n ≤ ((2 * h.n) ^ h.n) * NDelta ^ (h.n - 1) := by
          simpa [one_mul] using Nat.mul_le_mul_left ((2 * h.n) ^ h.n) hpow_ge_one
        _ ≤ Dist ^ h.n := hLower
    have hpow_lt : Dist ^ h.n < (2 * h.n) ^ h.n := by
      exact Nat.pow_lt_pow_left hlt (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hAmbient))
    exact (not_le_of_gt hpow_lt) hbase_le
  · intro hne hEq
    have hNpos : 1 ≤ NDelta := by
      have hneNonempty : (U ∆ V).Nonempty := by
        exact (Finset.symmDiff_nonempty).2 hne
      exact Nat.succ_le_of_lt (Finset.card_pos.mpr hneNonempty)
    have hbase_pos : 0 < (2 * h.n) ^ h.n := by
      positivity
    have hpow_le_one : NDelta ^ (h.n - 1) ≤ 1 := by
      have hmul :
          ((2 * h.n) ^ h.n) * NDelta ^ (h.n - 1) ≤ ((2 * h.n) ^ h.n) * 1 := by
        simpa [hEq] using hLower
      exact Nat.le_of_mul_le_mul_left hmul hbase_pos
    have hExp_ne : h.n - 1 ≠ 0 := by omega
    have hN_le_one : NDelta ≤ 1 := by
      exact
        (pow_le_one_iff_of_nonneg (show 0 ≤ NDelta by exact Nat.zero_le _) hExp_ne).mp hpow_le_one
    exact le_antisymm hN_le_one hNpos

end Omega.Conclusion
