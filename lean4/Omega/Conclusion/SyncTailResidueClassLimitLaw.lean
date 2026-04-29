import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-sync-tail-residue-class-limit-law`. -/
theorem paper_conclusion_sync_tail_residue_class_limit_law {p : ℕ}
    (residueLimit globalLimit : ℝ → Prop) (c : Fin p → ℝ)
    (hres : ∀ a : Fin p, residueLimit (c a))
    (hglobal_forces_equal : ∀ C : ℝ, globalLimit C → ∀ a : Fin p, c a = C)
    (hnot_constant : ¬ ∃ C : ℝ, ∀ a : Fin p, c a = C) :
    (∀ a : Fin p, residueLimit (c a)) ∧ ¬ ∃ C : ℝ, globalLimit C := by
  refine ⟨hres, ?_⟩
  rintro ⟨C, hC⟩
  exact hnot_constant ⟨C, hglobal_forces_equal C hC⟩

end Omega.Conclusion
