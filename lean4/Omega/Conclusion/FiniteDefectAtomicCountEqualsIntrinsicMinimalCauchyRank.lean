import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-finite-defect-atomic-count-equals-intrinsic-minimal-cauchy-rank`. -/
theorem paper_conclusion_finite_defect_atomic_count_equals_intrinsic_minimal_cauchy_rank
    (κ : ℕ)
    (admissibleRank : ℕ → Prop)
    (hLower : ∀ r, admissibleRank r → κ ≤ r)
    (hSharp : admissibleRank κ) :
    (∀ r, admissibleRank r → κ ≤ r) ∧ admissibleRank κ := by
  exact ⟨hLower, hSharp⟩

end Omega.Conclusion
