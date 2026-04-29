import Omega.Zeta.XiPrimeSliceNontrivialLayerExactMinimality

namespace Omega.Zeta

open Classical

/-- Paper label: `thm:xi-time-part9zq-active-primeslice-linear-growth`. -/
theorem paper_xi_time_part9zq_active_primeslice_linear_growth
    (T : XiPrimeSliceTower) (hbranch : ∀ i : Fin T.depth, T.branching i = true)
    (A : Finset (XiPrimeSliceBranchingLayer T)) (hA : Finset.univ ⊆ A) :
    T.depth ≤ A.card ∧
      ∃ Asharp : Finset (XiPrimeSliceBranchingLayer T), Asharp.card = T.depth := by
  let e : Fin T.depth ≃ XiPrimeSliceBranchingLayer T := {
    toFun i := ⟨i, hbranch i⟩
    invFun j := j.1
    left_inv i := rfl
    right_inv j := by
      cases j
      rfl }
  have hcard_type : Fintype.card (XiPrimeSliceBranchingLayer T) = T.depth := by
    calc
      Fintype.card (XiPrimeSliceBranchingLayer T) = Fintype.card (Fin T.depth) :=
        (Fintype.card_congr e).symm
      _ = T.depth := Fintype.card_fin T.depth
  have huniv_card : (Finset.univ : Finset (XiPrimeSliceBranchingLayer T)).card = T.depth := by
    simp [hcard_type]
  exact ⟨by simpa [huniv_card] using Finset.card_le_card hA, ⟨Finset.univ, huniv_card⟩⟩

end Omega.Zeta
