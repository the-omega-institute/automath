import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.Fiber

namespace Omega

open scoped BigOperators

/-- Jensen saturation for the finite fiber-multiplicity observable:
`E_π[log d_m(X)] ≤ log E_π[d_m(X)]`, with equality exactly when the positive-`π` support sees a
single fiber multiplicity. For the uniform visible baseline, the expected multiplicity is the
average fiber size `|Ω_m| / |X_m| = 2^m / |X_m|`.
    cor:fold-fiber-entropy-saturation -/
theorem paper_fold_fiber_entropy_saturation (m : ℕ) (π : X m → ℝ)
    (hπ_nonneg : ∀ x, 0 ≤ π x) (hπ_sum : Finset.univ.sum π = 1) :
    (∑ x : X m, π x * Real.log (X.fiberMultiplicity x) ≤
      Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ))) ∧
      ((∑ x : X m, π x * Real.log (X.fiberMultiplicity x) =
          Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ))) ↔
        ∀ x : X m, π x ≠ 0 →
          (X.fiberMultiplicity x : ℝ) = ∑ y : X m, π y * (X.fiberMultiplicity y : ℝ)) ∧
      (∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * (X.fiberMultiplicity x : ℝ) =
        ((2 : ℝ) ^ m) / Fintype.card (X m)) ∧
      (∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * Real.log (X.fiberMultiplicity x) ≤
        Real.log (((2 : ℝ) ^ m) / Fintype.card (X m))) := by
  have hConcave : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hStrictConcave : StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi
  have hmem :
      ∀ x ∈ (Finset.univ : Finset (X m)), ((X.fiberMultiplicity x : ℕ) : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    intro x hx
    show (0 : ℝ) < (X.fiberMultiplicity x : ℝ)
    exact_mod_cast X.fiberMultiplicity_pos x
  have hJensen :
      ∑ x : X m, π x * Real.log (X.fiberMultiplicity x) ≤
        Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ)) := by
    simpa [smul_eq_mul] using
      (ConcaveOn.le_map_sum
        (t := (Finset.univ : Finset (X m))) (w := π)
        (p := fun x : X m => (X.fiberMultiplicity x : ℝ))
        hConcave (by intro x hx; exact hπ_nonneg x) hπ_sum hmem)
  have hEqIff₀ :
      Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ)) =
        ∑ x : X m, π x * Real.log (X.fiberMultiplicity x) ↔
        ∀ x : X m, π x ≠ 0 →
          (X.fiberMultiplicity x : ℝ) = ∑ y : X m, π y * (X.fiberMultiplicity y : ℝ) := by
    simpa [smul_eq_mul] using
      (StrictConcaveOn.map_sum_eq_iff'
        (t := (Finset.univ : Finset (X m))) (w := π)
        (p := fun x : X m => (X.fiberMultiplicity x : ℝ))
        hStrictConcave (by intro x hx; exact hπ_nonneg x) hπ_sum hmem)
  have hEqIff :
      (∑ x : X m, π x * Real.log (X.fiberMultiplicity x) =
          Real.log (∑ x : X m, π x * (X.fiberMultiplicity x : ℝ))) ↔
        ∀ x : X m, π x ≠ 0 →
          (X.fiberMultiplicity x : ℝ) = ∑ y : X m, π y * (X.fiberMultiplicity y : ℝ) := by
    constructor
    · intro h
      exact hEqIff₀.mp h.symm
    · intro h
      exact (hEqIff₀.mpr h).symm
  have hcard_pos : 0 < (Fintype.card (X m) : ℝ) := by
    rw [X.card_eq_fib]
    exact_mod_cast fib_succ_pos (m + 1)
  have hUnif_nonneg : ∀ x : X m, 0 ≤ (1 : ℝ) / Fintype.card (X m) := by
    intro x
    positivity
  have hUnif_sum : ∑ x : X m, (1 : ℝ) / Fintype.card (X m) = 1 := by
    simp [hcard_pos.ne']
  have hUnifJensen :
      ∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * Real.log (X.fiberMultiplicity x) ≤
        Real.log (∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * (X.fiberMultiplicity x : ℝ)) := by
    simpa [smul_eq_mul] using
      (ConcaveOn.le_map_sum
        (t := (Finset.univ : Finset (X m)))
        (w := fun _ : X m => (1 : ℝ) / Fintype.card (X m))
        (p := fun x : X m => (X.fiberMultiplicity x : ℝ))
        hConcave (by intro x hx; exact hUnif_nonneg x) hUnif_sum hmem)
  have hUnifMean :
      ∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * (X.fiberMultiplicity x : ℝ) =
        ((2 : ℝ) ^ m) / Fintype.card (X m) := by
    calc
      ∑ x : X m, ((1 : ℝ) / Fintype.card (X m)) * (X.fiberMultiplicity x : ℝ) =
          ((1 : ℝ) / Fintype.card (X m)) * ∑ x : X m, (X.fiberMultiplicity x : ℝ) := by
            rw [Finset.mul_sum]
      _ = ((1 : ℝ) / Fintype.card (X m)) * ((2 ^ m : ℕ) : ℝ) := by
            congr 1
            exact_mod_cast X.fiberMultiplicity_sum_eq_pow m
      _ = ((1 : ℝ) / Fintype.card (X m)) * ((2 : ℝ) ^ m) := by
            congr 1
            exact_mod_cast (show 2 ^ m = 2 ^ m by rfl)
      _ = ((2 : ℝ) ^ m) / Fintype.card (X m) := by
            rw [div_eq_mul_inv]
            ring
  rw [hUnifMean] at hUnifJensen
  exact ⟨hJensen, hEqIff, hUnifMean, hUnifJensen⟩

end Omega
