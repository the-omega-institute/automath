import Omega.SPG.TanakaStokes

open scoped BigOperators

namespace Omega.SPG

/-- Paper label: `thm:spg-scan-tanaka-stokes`. -/
theorem paper_spg_scan_tanaka_stokes :
    (∀ x y : ℚ, 0 ≤ tanakaIncrement x y (1 / 2 : ℚ)) ∧
      (∀ (seq : ℕ → ℚ) (m : Nat),
        0 ≤ ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) (1 / 2 : ℚ)) ∧
      (∀ (seq : ℕ → ℚ) (m : Nat),
        ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) (1 / 2 : ℚ) ≤
          ∑ k ∈ Finset.range (m + 1), tanakaIncrement (seq k) (seq (k + 1)) (1 / 2 : ℚ)) ∧
      (∀ (seq : ℕ → ℚ) (m : Nat),
        |seq m - (1 / 2 : ℚ)| = |seq 0 - (1 / 2 : ℚ)| +
          ∑ k ∈ Finset.range m,
            (if seq k - (1 / 2 : ℚ) > 0 then 1 else if seq k - (1 / 2 : ℚ) < 0 then -1 else 0) *
              (seq (k + 1) - seq k) +
          ∑ k ∈ Finset.range m, tanakaIncrement (seq k) (seq (k + 1)) (1 / 2 : ℚ)) := by
  exact paper_scan_projection_address_tanaka_stokes_seeds

end Omega.SPG
