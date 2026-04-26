import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-realinput40-periodic-residue-moving-delta-mixture`. -/
theorem paper_conclusion_realinput40_periodic_residue_moving_delta_mixture
    {m : Nat} (Acore : Real) (anchor : Fin m) (core full : Fin m -> Real) (hcore : 0 < Acore)
    (hshift : ∀ r, full r = core r + 2 * (if r = anchor then 1 else 0))
    (hmass : ∑ r, core r = Acore) :
    (fun r => full r / (Acore + 2)) =
      fun r =>
        (Acore / (Acore + 2)) * (core r / Acore) +
          (2 / (Acore + 2)) * (if r = anchor then 1 else 0) := by
  let _ := hmass
  funext r
  have hA : Acore ≠ 0 := ne_of_gt hcore
  have hA2 : Acore + 2 ≠ 0 := by
    linarith
  rw [hshift r]
  by_cases hr : r = anchor
  · simp [hr]
    field_simp [hA, hA2]
  · simp [hr]
    field_simp [hA, hA2]

end Omega.Conclusion
