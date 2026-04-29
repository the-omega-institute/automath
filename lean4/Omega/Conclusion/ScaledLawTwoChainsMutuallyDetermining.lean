import Mathlib.Tactic

namespace Omega.Conclusion

/-- The common scaled-law invariant, represented by its two finite atomic weights. -/
def conclusion_scaled_law_two_chains_mutually_determining_invariant := ℝ × ℝ

/-- The odd-moment recovery chain records the sum and difference coordinates. -/
def conclusion_scaled_law_two_chains_mutually_determining_odd_chain
    (ν : conclusion_scaled_law_two_chains_mutually_determining_invariant) : ℝ × ℝ :=
  (ν.1 + ν.2, ν.1 - ν.2)

/-- The recoverability-profile chain records a nonzero scalar multiple of each coordinate. -/
def conclusion_scaled_law_two_chains_mutually_determining_recoverability_chain
    (ν : conclusion_scaled_law_two_chains_mutually_determining_invariant) : ℝ × ℝ :=
  (2 * ν.1, 2 * ν.2)

/-- Paper label: `cor:conclusion-scaled-law-two-chains-mutually-determining`.
Both recovery chains are injective maps into the same scaled-law invariant, so equality of either
chain is equivalent to equality of the other. -/
def conclusion_scaled_law_two_chains_mutually_determining_statement : Prop :=
  (∀ ν μ : conclusion_scaled_law_two_chains_mutually_determining_invariant,
      conclusion_scaled_law_two_chains_mutually_determining_odd_chain ν =
          conclusion_scaled_law_two_chains_mutually_determining_odd_chain μ →
        ν = μ) ∧
    (∀ ν μ : conclusion_scaled_law_two_chains_mutually_determining_invariant,
      conclusion_scaled_law_two_chains_mutually_determining_recoverability_chain ν =
          conclusion_scaled_law_two_chains_mutually_determining_recoverability_chain μ →
        ν = μ) ∧
    ∀ ν μ : conclusion_scaled_law_two_chains_mutually_determining_invariant,
      conclusion_scaled_law_two_chains_mutually_determining_odd_chain ν =
          conclusion_scaled_law_two_chains_mutually_determining_odd_chain μ ↔
        conclusion_scaled_law_two_chains_mutually_determining_recoverability_chain ν =
          conclusion_scaled_law_two_chains_mutually_determining_recoverability_chain μ

theorem paper_conclusion_scaled_law_two_chains_mutually_determining :
    conclusion_scaled_law_two_chains_mutually_determining_statement := by
  constructor
  · intro ν μ h
    rcases ν with ⟨ν₁, ν₂⟩
    rcases μ with ⟨μ₁, μ₂⟩
    simp [conclusion_scaled_law_two_chains_mutually_determining_odd_chain] at h ⊢
    exact Prod.ext (by linarith) (by linarith)
  constructor
  · intro ν μ h
    rcases ν with ⟨ν₁, ν₂⟩
    rcases μ with ⟨μ₁, μ₂⟩
    simp [conclusion_scaled_law_two_chains_mutually_determining_recoverability_chain] at h ⊢
    exact Prod.ext (by linarith) (by linarith)
  · intro ν μ
    constructor
    · intro h
      have hνμ : ν = μ := by
        rcases ν with ⟨ν₁, ν₂⟩
        rcases μ with ⟨μ₁, μ₂⟩
        simp [conclusion_scaled_law_two_chains_mutually_determining_odd_chain] at h ⊢
        exact Prod.ext (by linarith) (by linarith)
      rw [hνμ]
    · intro h
      have hνμ : ν = μ := by
        rcases ν with ⟨ν₁, ν₂⟩
        rcases μ with ⟨μ₁, μ₂⟩
        simp [conclusion_scaled_law_two_chains_mutually_determining_recoverability_chain] at h ⊢
        exact Prod.ext (by linarith) (by linarith)
      rw [hνμ]

end Omega.Conclusion
