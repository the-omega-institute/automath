import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part50dc-periodic-residue-rational-core-octic`. -/
theorem paper_xi_time_part50dc_periodic_residue_rational_core_octic (m : ℕ) (hm : 2 ≤ m)
    (fourierResolvent atomCoreSplit fullDenomBound coreDenomBound fullRecurrence
      coreRecurrence : Prop)
    (hFourier : fourierResolvent) (hSplit : fourierResolvent → atomCoreSplit)
    (hBounds :
      atomCoreSplit → fullDenomBound ∧ coreDenomBound ∧ fullRecurrence ∧ coreRecurrence) :
    atomCoreSplit ∧ fullDenomBound ∧ coreDenomBound ∧ fullRecurrence ∧ coreRecurrence := by
  have _ : 2 ≤ m := hm
  have hAtom : atomCoreSplit := hSplit hFourier
  rcases hBounds hAtom with ⟨hFullDenom, hCoreDenom, hFullRecurrence, hCoreRecurrence⟩
  exact ⟨hAtom, hFullDenom, hCoreDenom, hFullRecurrence, hCoreRecurrence⟩

end Omega.Zeta
