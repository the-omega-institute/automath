import Mathlib.Tactic

namespace Omega.GroupUnification.SpreadEquivalence

/-- Both deviations from endpoints are bounded by the spread.
    cor:gut-A-spread-equivalence -/
theorem avg_deviation_le_spread (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    |b - a| ≤ c - a ∧ |b - c| ≤ c - a := by
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith)]; linarith

/-- The max deviation is at least half the spread.
    cor:gut-A-spread-equivalence -/
theorem max_deviation_ge_half_spread (a x c : ℝ) (_hax : a ≤ x) (_hxc : x ≤ c) :
    (c - a) / 2 ≤ max (x - a) (c - x) := by
  have h1 : (x - a) + (c - x) = c - a := by ring
  have h2 : (c - a) / 2 ≤ (x - a) ∨ (c - a) / 2 ≤ (c - x) := by
    by_contra hcon
    push_neg at hcon
    linarith [hcon.1, hcon.2]
  rcases h2 with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right h

/-- Paper package: spread equivalence — half-spread ≤ max-dev ≤ spread.
    cor:gut-A-spread-equivalence -/
theorem paper_gut_A_spread_equivalence (a x c : ℝ) (hax : a ≤ x) (hxc : x ≤ c) :
    (c - a) / 2 ≤ max (x - a) (c - x) ∧ max (x - a) (c - x) ≤ c - a := by
  refine ⟨max_deviation_ge_half_spread a x c hax hxc, ?_⟩
  exact max_le (by linarith) (by linarith)

end Omega.GroupUnification.SpreadEquivalence
