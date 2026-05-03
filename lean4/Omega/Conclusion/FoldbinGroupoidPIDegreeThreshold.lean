import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-groupoid-pi-degree-threshold`. -/
theorem paper_conclusion_foldbin_groupoid_pi_degree_threshold (D PIdeg : ℕ)
    (satisfiesStandard : ℕ → Prop) (hPI : PIdeg = D)
    (hThreshold : ∀ r, satisfiesStandard r ↔ D ≤ r) :
    PIdeg = D ∧ satisfiesStandard D ∧ ∀ r, r < D → ¬ satisfiesStandard r := by
  refine ⟨hPI, ?_, ?_⟩
  · exact (hThreshold D).mpr le_rfl
  · intro r hr hSat
    exact Nat.not_lt_of_ge ((hThreshold r).mp hSat) hr

end Omega.Conclusion
