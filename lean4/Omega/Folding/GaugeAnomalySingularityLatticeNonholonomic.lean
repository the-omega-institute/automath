import Mathlib.Tactic

namespace Omega.Folding

/-- A `ℤ`-indexed lattice of singular shifts forces infinitely many singularities, hence the
chapter's abstract obstruction wrapper yields non-`D`-finiteness.
    thm:fold-gauge-anomaly-singularity-lattice-nonholonomic -/
theorem paper_fold_gauge_anomaly_singularity_lattice_nonholonomic (Sing : Set ℂ) (θ : ℂ)
    (nonDFinite : Prop)
    (hLattice : ∀ k : ℤ, θ + (2 * Real.pi * Complex.I) * k ∈ Sing)
    (hInj : Function.Injective (fun k : ℤ => θ + (2 * Real.pi * Complex.I) * k))
    (hNonDFinite : Set.Infinite Sing → nonDFinite) : Set.Infinite Sing ∧ nonDFinite := by
  have hRangeInfinite : Set.Infinite (Set.range fun k : ℤ => θ + (2 * Real.pi * Complex.I) * k) :=
    Set.infinite_range_of_injective hInj
  have hSingInfinite : Set.Infinite Sing := by
    refine hRangeInfinite.mono ?_
    intro z hz
    rcases hz with ⟨k, rfl⟩
    exact hLattice k
  exact ⟨hSingInfinite, hNonDFinite hSingInfinite⟩

end Omega.Folding
