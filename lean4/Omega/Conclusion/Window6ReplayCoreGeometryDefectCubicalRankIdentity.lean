import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-replay-core-geometry-defect-cubical-rank-identity`. -/
theorem paper_conclusion_window6_replay_core_geometry_defect_cubical_rank_identity
    (bInv quotientDim rCube : Nat) (hb : bInv = 2) (hq : quotientDim = 2)
    (hr : rCube = 2) :
    bInv = quotientDim /\ quotientDim = rCube /\ rCube = 2 := by
  subst bInv
  subst quotientDim
  exact ⟨rfl, hr.symm, hr⟩

end Omega.Conclusion
