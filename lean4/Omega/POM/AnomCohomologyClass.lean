import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-anom-cohomology-class`. -/
theorem paper_pom_anom_cohomology_class {W C A Q : Type*} [AddGroup A] [AddGroup Q]
    (classOf : A → Q) (hadd : ∀ x y, classOf (x + y) = classOf x + classOf y)
    (hzero : classOf 0 = 0) (boundary : C → A) (anom anom' : W → A)
    (hchange : ∀ w, ∃ c, anom' w = anom w + boundary c)
    (hboundary : ∀ c, classOf (boundary c) = 0) :
    ∀ w, classOf (anom w) = 0 ↔ classOf (anom' w) = 0 := by
  intro w
  rcases hchange w with ⟨c, hc⟩
  have hboundaryZero : classOf (boundary c) = classOf (0 : A) := by
    rw [hboundary c, hzero]
  have hclass : classOf (anom' w) = classOf (anom w) := by
    rw [hc, hadd, hboundaryZero, hzero, add_zero]
  constructor
  · intro h
    simpa [hclass] using h
  · intro h
    simpa [hclass] using h

end Omega.POM
