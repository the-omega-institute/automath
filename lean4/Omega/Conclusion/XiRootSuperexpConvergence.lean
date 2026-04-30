namespace Omega.Conclusion

/-- Combine Rouche stability with the explicit dyadic tail estimate. -/
theorem conclusion_xi_root_superexp_convergence_from_rouche_tail
    (roucheStability explicitTailBound uniqueZero superexpBound : Prop)
    (hRouche : roucheStability) (hTail : explicitTailBound)
    (hUse : roucheStability → explicitTailBound → uniqueZero ∧ superexpBound) :
    uniqueZero ∧ superexpBound := by
  exact hUse hRouche hTail

/-- Paper label: `cor:conclusion-xi-root-superexp-convergence`. -/
theorem paper_conclusion_xi_root_superexp_convergence
    (roucheStability explicitTailBound uniqueZero superexpBound : Prop)
    (hRouche : roucheStability) (hTail : explicitTailBound)
    (hUse : roucheStability → explicitTailBound → uniqueZero ∧ superexpBound) :
    uniqueZero ∧ superexpBound := by
  exact conclusion_xi_root_superexp_convergence_from_rouche_tail
    roucheStability explicitTailBound uniqueZero superexpBound hRouche hTail hUse

end Omega.Conclusion
