namespace Omega.Zeta

/-- Paper label: `thm:xi-unified-verifier-three-budget-orthogonality`. -/
theorem paper_xi_unified_verifier_three_budget_orthogonality
    (radialOK addressOK endpointOK success : Prop)
    (hsuccess : success ↔ radialOK ∧ addressOK ∧ endpointOK) :
    (¬ success ↔ ¬ radialOK ∨ ¬ addressOK ∨ ¬ endpointOK) := by
  constructor
  · intro hfail
    by_cases hr : radialOK
    · by_cases ha : addressOK
      · by_cases he : endpointOK
        · exact False.elim (hfail (hsuccess.mpr ⟨hr, ha, he⟩))
        · exact Or.inr (Or.inr he)
      · exact Or.inr (Or.inl ha)
    · exact Or.inl hr
  · intro hbad hsucc
    rcases hsuccess.mp hsucc with ⟨hr, ha, he⟩
    rcases hbad with hbad | hbad | hbad
    · exact hbad hr
    · exact hbad ha
    · exact hbad he

end Omega.Zeta
