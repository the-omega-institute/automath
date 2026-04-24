import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

/-- Concrete Cayley/disk data for transporting completed-zeta zeros between the off-critical
half-strip and the unit disk. -/
structure AppRhIffDiskZeroFreeData where
  Zero : Type
  DiskPoint : Type
  cayley : Zero → DiskPoint
  insideDisk : DiskPoint → Prop
  completedZeta : Zero → ℂ
  diskModel : DiskPoint → ℂ
  offCritical : Zero → Prop
  forward_transport :
    ∀ z, completedZeta z = 0 → offCritical z →
      insideDisk (cayley z) ∧ diskModel (cayley z) = 0
  backward_transport :
    ∀ w, insideDisk w → diskModel w = 0 →
      ∃ z, completedZeta z = 0 ∧ offCritical z

namespace AppRhIffDiskZeroFreeData

/-- RH in this local model means that every completed-zeta zero lies on the critical line. -/
def riemannHypothesis (D : AppRhIffDiskZeroFreeData) : Prop :=
  ∀ z, D.completedZeta z = 0 → ¬ D.offCritical z

/-- The disk model is zero-free on the open unit disk. -/
def diskZeroFree (D : AppRhIffDiskZeroFreeData) : Prop :=
  ∀ w, D.insideDisk w → D.diskModel w ≠ 0

end AppRhIffDiskZeroFreeData

open AppRhIffDiskZeroFreeData

/-- The Cayley-model disk is zero-free exactly when the completed zeta function has no
off-critical zero.
    thm:app-rh-iff-disk-zero-free -/
theorem paper_app_rh_iff_disk_zero_free (D : AppRhIffDiskZeroFreeData) :
    D.riemannHypothesis ↔ D.diskZeroFree := by
  constructor
  · intro hRH w hw hzero
    rcases D.backward_transport w hw hzero with ⟨z, hzeta, hzoff⟩
    exact (hRH z hzeta hzoff).elim
  · intro hDisk z hzeta hzoff
    have hForward := D.forward_transport z hzeta hzoff
    exact hDisk (D.cayley z) hForward.1 hForward.2

end Omega.UnitCirclePhaseArithmetic
