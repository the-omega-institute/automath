import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete spectral-only audit package for the conclusion-level zeta-completeness obstruction.
From level `3` onward the spectral datum is constant, while the canonical synchronization budget is
`m - 1`. -/
structure conclusion_zeta_complete_audit_not_sync_complete_data where
  SpectralData : Type
  spectralData : ℕ → SpectralData
  syncBudget : ℕ → ℕ
  spectralData_eq_of_ge_three :
    ∀ {m n : ℕ}, 3 ≤ m → 3 ≤ n → spectralData m = spectralData n
  syncBudget_eq_sub_one : ∀ m : ℕ, 3 ≤ m → syncBudget m = m - 1

/-- Paper label: `cor:conclusion-zeta-complete-audit-not-sync-complete`. A decoder that sees only
the spectral channel cannot recover the synchronization budget, since levels `3` and `4` have the
same spectral datum but budgets `2` and `3`. -/
theorem paper_conclusion_zeta_complete_audit_not_sync_complete
    (D : conclusion_zeta_complete_audit_not_sync_complete_data) :
    ¬ ∃ decode : D.SpectralData → ℕ, ∀ m : ℕ, 3 ≤ m →
      decode (D.spectralData m) = D.syncBudget m := by
  rintro ⟨decode, hdecode⟩
  have hspec : D.spectralData 3 = D.spectralData 4 :=
    D.spectralData_eq_of_ge_three (by norm_num) (by norm_num)
  have hbudget :
      D.syncBudget 3 = D.syncBudget 4 := by
    calc
      D.syncBudget 3 = decode (D.spectralData 3) := (hdecode 3 (by norm_num)).symm
      _ = decode (D.spectralData 4) := by rw [hspec]
      _ = D.syncBudget 4 := hdecode 4 (by norm_num)
  rw [D.syncBudget_eq_sub_one 3 (by norm_num), D.syncBudget_eq_sub_one 4 (by norm_num)] at hbudget
  norm_num at hbudget

end Omega.Conclusion
