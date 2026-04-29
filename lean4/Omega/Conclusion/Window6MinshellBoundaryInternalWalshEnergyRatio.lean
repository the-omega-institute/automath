import Mathlib.Tactic
import Omega.Conclusion.Window6MinimalShellRigidSubcoverRootSlice

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-window6-minshell-boundary-internal-walsh-energy-ratio`.
On the eight-point minimal shell, the Plancherel/`χ²` conversion sends collision probabilities
`1/3` and `1/5` to the Walsh energies `5/3` and `3/5`, so their ratio is `25/9`. -/
theorem paper_conclusion_window6_minshell_boundary_internal_walsh_energy_ratio
    (colBoundary colInternal : ℚ) (hB : colBoundary = 1 / 3) (hI : colInternal = 1 / 5) :
    ((8 : ℚ) * (colBoundary - 1 / 8)) / ((8 : ℚ) * (colInternal - 1 / 8)) = 25 / 9 := by
  rw [hB, hI]
  norm_num

end Omega.Conclusion
