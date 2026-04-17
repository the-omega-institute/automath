import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Paper-facing finite-realizability package for the Nat-valued algebraic-degree axis:
any nonempty finite family of candidate degrees has a least realized witness.
    prop:gcdim-two-axis-finiteness -/
theorem paper_gcdim_two_axis_finiteness (basisDegrees : Finset ℕ) (hbasis : basisDegrees.Nonempty) :
    ∃ d_min ∈ basisDegrees, ∀ d ∈ basisDegrees, d_min ≤ d := by
  refine ⟨basisDegrees.min' hbasis, Finset.min'_mem basisDegrees hbasis, ?_⟩
  intro d hd
  exact Finset.min'_le basisDegrees d hd

end Omega.CircleDimension
