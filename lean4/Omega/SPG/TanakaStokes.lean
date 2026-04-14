import Omega.SPG.TanakaIncrement

open scoped BigOperators

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Paper-facing seed for the Tanaka identity at the threshold `1/2` used in the
    scan-projection clarity argument.
    thm:tanaka-stokes -/
theorem paper_scan_projection_address_tanaka_stokes_seeds :
    (∀ x y : ℚ, 0 ≤ tanakaIncrement x y (1 / 2 : ℚ)) ∧
      (∀ (seq : ℕ → ℚ) (m : Nat),
        0 ≤ ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) (1 / 2 : ℚ)) ∧
      (∀ (seq : ℕ → ℚ) (m : Nat),
        ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) (1 / 2 : ℚ) ≤
          ∑ k ∈ Finset.range (m + 1), tanakaIncrement (seq k) (seq (k + 1)) (1 / 2 : ℚ)) ∧
      (∀ (seq : ℕ → ℚ) (m : Nat),
        |seq m - (1 / 2 : ℚ)| = |seq 0 - (1 / 2 : ℚ)| +
          ∑ k ∈ Finset.range m,
            (if seq k - (1 / 2 : ℚ) > 0 then 1
             else if seq k - (1 / 2 : ℚ) < 0 then -1 else 0) *
              (seq (k + 1) - seq k) +
          ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) (1 / 2 : ℚ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    simpa using tanakaIncrement_nonneg x y (1 / 2 : ℚ)
  · intro seq m
    simpa using tanakaLocalTime_nonneg seq (1 / 2 : ℚ) m
  · intro seq m
    simpa using tanakaLocalTime_mono seq (1 / 2 : ℚ) m
  · intro seq m
    simpa using tanakaDecomposition seq (1 / 2 : ℚ) m

end Omega.SPG
