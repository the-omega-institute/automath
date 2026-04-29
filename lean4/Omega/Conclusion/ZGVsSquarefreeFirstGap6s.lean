namespace Omega.Conclusion

/-- thm:conclusion-zg-vs-squarefree-first-gap-6s -/
theorem paper_conclusion_zg_vs_squarefree_first_gap_6s
    (excludedFirstIsSix tailStartsAtFifteen dirichletGapAsymptotic scaledLimitOne : Prop)
    (hFirst : excludedFirstIsSix)
    (hTail : tailStartsAtFifteen)
    (hAsymp : dirichletGapAsymptotic)
    (hLimit : scaledLimitOne) :
    excludedFirstIsSix ∧ tailStartsAtFifteen ∧ dirichletGapAsymptotic ∧ scaledLimitOne := by
  exact ⟨hFirst, hTail, hAsymp, hLimit⟩

end Omega.Conclusion
