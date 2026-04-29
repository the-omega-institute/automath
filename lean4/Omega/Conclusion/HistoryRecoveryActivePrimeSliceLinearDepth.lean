import Omega.Zeta.XiPrimeSliceNontrivialLayerExactMinimality

namespace Omega.Conclusion

open Classical

/-- Paper label: `cor:conclusion-history-recovery-active-prime-slice-linear-depth`. -/
theorem paper_conclusion_history_recovery_active_prime_slice_linear_depth
    (T : Omega.Zeta.XiPrimeSliceTower)
    (hbranch : ∀ i : Fin T.depth, T.branching i = true)
    (A : Finset (Omega.Zeta.XiPrimeSliceBranchingLayer T)) (hA : Finset.univ ⊆ A) :
    T.depth ≤ A.card ∧
      ∃ Asharp : Finset (Omega.Zeta.XiPrimeSliceBranchingLayer T), Asharp.card = T.depth := by
  let e : Fin T.depth ≃ Omega.Zeta.XiPrimeSliceBranchingLayer T := {
    toFun i := ⟨i, hbranch i⟩
    invFun j := j.1
    left_inv i := rfl
    right_inv j := by
      cases j
      rfl }
  have hcard_type : Fintype.card (Omega.Zeta.XiPrimeSliceBranchingLayer T) = T.depth := by
    calc
      Fintype.card (Omega.Zeta.XiPrimeSliceBranchingLayer T) = Fintype.card (Fin T.depth) :=
        (Fintype.card_congr e).symm
      _ = T.depth := Fintype.card_fin T.depth
  have huniv_card : (Finset.univ : Finset (Omega.Zeta.XiPrimeSliceBranchingLayer T)).card =
      T.depth := by
    simp [hcard_type]
  exact ⟨by simpa [huniv_card] using Finset.card_le_card hA, ⟨Finset.univ, huniv_card⟩⟩

end Omega.Conclusion
