import Omega.Folding.PhiSlidingBlockCode

namespace Omega.Folding

/-- Concrete data for the sliding-block map `Φ_m` together with the source and target shifts. -/
structure phi_m_equivariant_data where
  A : Type*
  B : Type*
  m : ℕ
  localRule : (Fin m → A) → B

namespace phi_m_equivariant_data

/-- The source shift, sliding-block map, and target shift commute. -/
def shift_commutes (D : phi_m_equivariant_data) : Prop :=
  ∀ s : ℤ → D.A,
    slideBlockCode D.m D.localRule (shiftSeq s) = shiftSeq (slideBlockCode D.m D.localRule s)

end phi_m_equivariant_data

open phi_m_equivariant_data

/-- Paper label: `prop:Phi_m-equivariant`. The sliding-block map commutes with the time shift. -/
theorem paper_phi_m_equivariant (D : phi_m_equivariant_data) : D.shift_commutes := by
  intro s
  exact slideBlockCode_shift_equivariant D.m D.localRule s

end Omega.Folding
