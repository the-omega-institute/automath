import Omega.SPG.TanakaIncrement

namespace Omega.SPG

open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- Publication-facing core for the discrete Tanaka representation at threshold `1 / 2`.
    The Lean theorem records the nonnegativity and monotonicity of the discrete local time and
    the exact Tanaka decomposition for an arbitrary rational sequence.
    thm:scan-tanaka -/
theorem paper_prefix_scan_error_tanaka_representation
    (seq : ℕ → ℚ) :
    (∀ m : ℕ,
      0 ≤ ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) ((1 : ℚ) / 2)) ∧
    (∀ m : ℕ,
      ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) ((1 : ℚ) / 2) ≤
        ∑ k ∈ Finset.range (m + 1), tanakaIncrement (seq k) (seq (k + 1)) ((1 : ℚ) / 2)) ∧
    (∀ m : ℕ,
      |seq m - ((1 : ℚ) / 2)| = |seq 0 - ((1 : ℚ) / 2)| +
        ∑ k ∈ Finset.range m,
          (if seq k - ((1 : ℚ) / 2) > 0 then 1
            else if seq k - ((1 : ℚ) / 2) < 0 then -1 else 0) * (seq (k + 1) - seq k) +
        ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) ((1 : ℚ) / 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    exact tanakaLocalTime_nonneg seq ((1 : ℚ) / 2) m
  · intro m
    exact tanakaLocalTime_mono seq ((1 : ℚ) / 2) m
  · intro m
    exact tanakaDecomposition seq ((1 : ℚ) / 2) m

end Omega.SPG
