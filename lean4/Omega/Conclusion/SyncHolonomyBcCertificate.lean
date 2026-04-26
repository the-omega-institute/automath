import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sync-holonomy-bc-certificate`. A finite comparison surface has
nonnegative total synchronization holonomy, preserves the supplied gauge-invariance certificate,
and vanishes exactly when every local Beck--Chevalley defect vanishes. -/
theorem paper_conclusion_sync_holonomy_bc_certificate
    {ι : Type*} [Fintype ι] (kappa : ι → ℝ) (gaugeInvariant strictBC : Prop)
    (hnonneg : ∀ i, 0 ≤ kappa i) (hinv : gaugeInvariant)
    (hstrict : (∀ i, kappa i = 0) ↔ strictBC) :
    0 ≤ ∑ i, kappa i ∧ gaugeInvariant ∧ ((∑ i, kappa i = 0) ↔ strictBC) := by
  refine ⟨?_, hinv, ?_⟩
  · exact Finset.sum_nonneg fun i _ => hnonneg i
  · constructor
    · intro hsum
      exact hstrict.mp fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i (by simp)
    · intro hbc
      exact Finset.sum_eq_zero fun i _ => hstrict.mpr hbc i

end Omega.Conclusion
