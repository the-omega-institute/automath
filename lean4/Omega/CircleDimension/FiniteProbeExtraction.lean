import Mathlib.Tactic

namespace Omega.CircleDimension.FiniteProbeExtraction

/-- A single truncation level contributes one unit exactly when the exponent reaches that level.
    thm:cdim-finite-probe-extraction -/
theorem min_truncation_step
    (a k : ℕ) (hk : 1 ≤ k) :
    min a k - min a (k - 1) = if k ≤ a then 1 else 0 := by
  by_cases h : k ≤ a
  · have h1 : min a k = k := by omega
    have h2 : min a (k - 1) = k - 1 := by omega
    rw [h1, h2, if_pos h]
    omega
  · have h1 : min a k = a := by omega
    have h2 : min a (k - 1) = a := by omega
    rw [h1, h2, if_neg h]
    omega

/-- The finite probe difference recovers the number of exponents at least `k`.
    thm:cdim-finite-probe-extraction -/
theorem paper_cdim_finite_probe_extraction_seeds
    (α : List ℕ) (k : ℕ) (hk : 1 ≤ k) :
    let bp : ℕ → ℕ := fun j => (α.map (fun a => min a j)).sum
    bp k - bp (k - 1) = α.countP (fun a => k ≤ a) := by
  have hsum :
      (α.map (fun a => min a k)).sum =
        (α.map (fun a => min a (k - 1))).sum + α.countP (fun a => k ≤ a) := by
    induction α with
    | nil =>
        simp
    | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, List.countP_cons]
        by_cases h : k ≤ a
        · simp [h]
          have h2 : min a (k - 1) = k - 1 := by omega
          rw [h2, ih]
          omega
        · simp [h]
          have h2 : min a (k - 1) = a := by omega
          rw [h2, ih]
          omega
  simp only
  rw [hsum]
  omega

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_cdim_finite_probe_extraction_package
    (α : List ℕ) (k : ℕ) (hk : 1 ≤ k) :
    let bp : ℕ → ℕ := fun j => (α.map (fun a => min a j)).sum
    bp k - bp (k - 1) = α.countP (fun a => k ≤ a) :=
  paper_cdim_finite_probe_extraction_seeds α k hk

end Omega.CircleDimension.FiniteProbeExtraction
