import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-local-index-binary-log-symmetry-surcharge`. -/
theorem paper_conclusion_window6_local_index_binary_log_symmetry_surcharge
    (bInv index boundaryBits centerBits : Nat) (hIndex : index = 4) (hInv : bInv = 2)
    (hBoundary : 3 ≤ boundaryBits) (hCenter : 4 ≤ centerBits) :
    bInv = 2 ∧ index = 4 ∧ 1 ≤ boundaryBits - bInv ∧ 2 ≤ centerBits - bInv := by
  subst index
  subst bInv
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> omega

end Omega.Conclusion
