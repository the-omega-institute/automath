namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-halting-measure-atomic-branch`. -/
theorem paper_conclusion_halting_measure_atomic_branch
    (halts pureAtomic exactDim : Prop) (h_nonhalt : ¬ halts → pureAtomic)
    (h_halt : halts → ¬ pureAtomic ∧ exactDim) :
    (pureAtomic ↔ ¬ halts) ∧ (halts → exactDim) := by
  constructor
  · constructor
    · intro hp hh
      exact (h_halt hh).1 hp
    · intro hnh
      exact h_nonhalt hnh
  · intro hh
    exact (h_halt hh).2

end Omega.Conclusion
