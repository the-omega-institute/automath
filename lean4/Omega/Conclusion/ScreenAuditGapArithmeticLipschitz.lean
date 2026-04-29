import Mathlib.Data.Nat.Basic

/-- Paper label: `thm:conclusion-screen-audit-gap-arithmetic-lipschitz`. -/
theorem paper_conclusion_screen_audit_gap_arithmetic_lipschitz {Screen Code : Type}
    (auditGapDistance : Screen → Screen → ℕ) (arithCode : Screen → Code)
    (arithDist : Code → Code → ℕ) (symmDiff : Screen → Screen → ℕ) (basis : Screen → Prop)
    (connectedByTwoStepExchange : Screen → Screen → Prop)
    (hDist : ∀ S T, arithDist (arithCode S) (arithCode T) = symmDiff S T)
    (hLip : ∀ S T, auditGapDistance S T ≤ symmDiff S T)
    (hSharp : ∃ S T, auditGapDistance S T = 1 ∧ symmDiff S T = 1)
    (hConn : ∀ B B', basis B → basis B' → connectedByTwoStepExchange B B') :
    (∀ S T, auditGapDistance S T ≤ arithDist (arithCode S) (arithCode T)) ∧
      (∃ S T, auditGapDistance S T = 1 ∧ arithDist (arithCode S) (arithCode T) = 1) ∧
        (∀ B B', basis B → basis B' → connectedByTwoStepExchange B B') := by
  refine ⟨?_, ?_, hConn⟩
  · intro S T
    rw [hDist S T]
    exact hLip S T
  · rcases hSharp with ⟨S, T, hAudit, hSymm⟩
    refine ⟨S, T, hAudit, ?_⟩
    rw [hDist S T, hSymm]
