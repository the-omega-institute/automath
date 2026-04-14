import Mathlib.Tactic

/-!
# Minimum latches equals ceiling log₂ of states

For a sequential transducer π with s(π) states, the minimum number of
latch bits m(π) needed for a synchronous Boolean circuit realization
satisfies m(π) = ⌈log₂ s(π)⌉.

We verify the clog₂ seed values and the encoding bound.
-/

namespace Omega.Conclusion.MinLatchesLogStates

/-! ## Seed values for Nat.clog 2 -/

/-- Nat.clog 2 seed values: ⌈log₂ 1⌉=0, ⌈log₂ 2⌉=1, ⌈log₂ 3⌉=2,
    ⌈log₂ 4⌉=2, ⌈log₂ 5⌉=3, ⌈log₂ 8⌉=3, ⌈log₂ 9⌉=4.
    prop:conclusion-min-latches-equals-log-states -/
theorem paper_conclusion_min_latches_log_states :
    Nat.clog 2 1 = 0 ∧ Nat.clog 2 2 = 1 ∧ Nat.clog 2 3 = 2 ∧
    Nat.clog 2 4 = 2 ∧ Nat.clog 2 5 = 3 ∧ Nat.clog 2 8 = 3 ∧
    Nat.clog 2 9 = 4 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- The encoding bound: s states fit in m = ⌈log₂ s⌉ bits, i.e. s ≤ 2^m.
    Verified for the seed values.
    prop:conclusion-min-latches-equals-log-states -/
theorem clog_encoding_bound :
    1 ≤ 2 ^ Nat.clog 2 1 ∧ 2 ≤ 2 ^ Nat.clog 2 2 ∧
    3 ≤ 2 ^ Nat.clog 2 3 ∧ 4 ≤ 2 ^ Nat.clog 2 4 ∧
    5 ≤ 2 ^ Nat.clog 2 5 ∧ 8 ≤ 2 ^ Nat.clog 2 8 ∧
    9 ≤ 2 ^ Nat.clog 2 9 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Tightness: reducing m by 1 no longer fits s states.
    Verified for s ∈ {3, 5, 9} (non-power-of-2 cases).
    prop:conclusion-min-latches-equals-log-states -/
theorem clog_tightness :
    ¬(3 ≤ 2 ^ (Nat.clog 2 3 - 1)) ∧
    ¬(5 ≤ 2 ^ (Nat.clog 2 5 - 1)) ∧
    ¬(9 ≤ 2 ^ (Nat.clog 2 9 - 1)) := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- Extended clog seed: ⌈log₂ 16⌉=4, ⌈log₂ 17⌉=5, ⌈log₂ 21⌉=5 (|X_6|=21),
    ⌈log₂ 32⌉=5, ⌈log₂ 33⌉=6.
    prop:conclusion-min-latches-equals-log-states -/
theorem clog_extended_seeds :
    Nat.clog 2 16 = 4 ∧ Nat.clog 2 17 = 5 ∧
    Nat.clog 2 21 = 5 ∧ Nat.clog 2 32 = 5 ∧ Nat.clog 2 33 = 6 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide⟩

/-- Encoding bound for extended seeds.
    prop:conclusion-min-latches-equals-log-states -/
theorem clog_encoding_bound_extended :
    21 ≤ 2 ^ Nat.clog 2 21 ∧ 33 ≤ 2 ^ Nat.clog 2 33 := by
  refine ⟨by native_decide, by native_decide⟩

/-- Paper package: min-latches-log-states full seeds.
    prop:conclusion-min-latches-equals-log-states -/
theorem paper_conclusion_min_latches_full :
    Nat.clog 2 1 = 0 ∧ Nat.clog 2 2 = 1 ∧ Nat.clog 2 3 = 2 ∧
    Nat.clog 2 4 = 2 ∧ Nat.clog 2 5 = 3 ∧ Nat.clog 2 8 = 3 ∧
    Nat.clog 2 9 = 4 ∧ Nat.clog 2 21 = 5 ∧ Nat.clog 2 33 = 6 := by
  refine ⟨by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide,
          by native_decide, by native_decide, by native_decide⟩

end Omega.Conclusion.MinLatchesLogStates
