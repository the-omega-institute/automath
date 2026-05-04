namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-regular-singular-no-finite-abelian-ledger`. -/
theorem paper_conclusion_regular_singular_no_finite_abelian_ledger
    (finiteAbelianLedger normalClosureNonabelian : Prop)
    (hledger_forces_abelian : finiteAbelianLedger → ¬ normalClosureNonabelian)
    (hnonabelian : normalClosureNonabelian) :
    ¬ finiteAbelianLedger := by
  intro hledger
  exact hledger_forces_abelian hledger hnonabelian

end Omega.Conclusion
