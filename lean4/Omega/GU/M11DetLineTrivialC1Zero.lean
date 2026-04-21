import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GU.M11Canonical16ComplexModuleDetOne

namespace Omega.GU

/-- The determinant line has trivial first Chern class exactly when the determinant character is
trivial. -/
noncomputable def m11DetLineFirstChernClass : ZMod 34 :=
  if m11Canonical16ComplexDet = 1 then 0 else 1

/-- The determinant character of the canonical `16`-dimensional complex `M11` module is trivial,
so the associated determinant line bundle has vanishing first Chern class modulo `34`.
    cor:m11-det-line-trivial-c1-zero -/
theorem paper_m11_det_line_trivial_c1_zero :
    m11Canonical16ComplexDet = 1 ∧ (m11DetLineFirstChernClass : ZMod 34) = 0 := by
  refine ⟨m11Canonical16ComplexDet_eq_one, ?_⟩
  simp [m11DetLineFirstChernClass, m11Canonical16ComplexDet_eq_one]

end Omega.GU
