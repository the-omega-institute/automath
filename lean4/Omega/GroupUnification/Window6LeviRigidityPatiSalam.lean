import Omega.GroupUnification.Window6CommonRefinementSMLevi

namespace Omega.GroupUnification

/-- Lie-algebra-level rigidity for the audited `21 = 15 ⊕ 3 ⊕ 3` window-6 Levi skeleton.
    cor:window6-levi-rigidity-pati-salam -/
theorem paper_window6_levi_rigidity_pati_salam :
    window6PatiSalamAdjointDim = 21 ∧
      window6CommonRefinementPatiSalamData.globalFormIsSU4xSU2xSU2 := by
  rcases paper_window6_common_refinement_sm_levi with
    ⟨_, hdim, _, hglobal, _, _, _⟩
  exact ⟨hdim, hglobal⟩

end Omega.GroupUnification
