import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-golden-atom-double-local-fission-at-2-and-5`. -/
theorem paper_conclusion_realinput40_golden_atom_double_local_fission_at_2_and_5
    (irreducibleAt5 splitOverQ5Sqrt5 doubleRootMod2 incompatibleLocalShapes : Prop)
    (h5 : irreducibleAt5 ∧ splitOverQ5Sqrt5)
    (h2 : doubleRootMod2)
    (hlocal :
      irreducibleAt5 ∧ splitOverQ5Sqrt5 -> doubleRootMod2 -> incompatibleLocalShapes) :
    incompatibleLocalShapes := by
  exact hlocal h5 h2

end Omega.Conclusion
