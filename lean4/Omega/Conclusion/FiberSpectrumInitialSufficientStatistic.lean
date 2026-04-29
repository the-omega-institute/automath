import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-fiber-spectrum-initial-sufficient-statistic`. -/
theorem paper_conclusion_fiber_spectrum_initial_sufficient_statistic {α σ ν : Type}
    (Spec : α → σ) (I : α → ν) (hI : ∀ x y, Spec x = Spec y → I x = I y) :
    ∃! Itilde : Set.range Spec → ν, ∀ x : α, Itilde ⟨Spec x, ⟨x, rfl⟩⟩ = I x := by
  classical
  let Itilde : Set.range Spec → ν := fun s => I (Classical.choose s.2)
  have hdesc : ∀ x : α, Itilde ⟨Spec x, ⟨x, rfl⟩⟩ = I x := by
    intro x
    have hchoose : Spec (Classical.choose (show ∃ y, Spec y = Spec x from ⟨x, rfl⟩)) =
        Spec x :=
      Classical.choose_spec (show ∃ y, Spec y = Spec x from ⟨x, rfl⟩)
    exact hI _ x hchoose
  refine ⟨Itilde, hdesc, ?_⟩
  intro J hJ
  funext s
  rcases s with ⟨_, x, rfl⟩
  rw [hdesc x, hJ x]

end Omega.Conclusion
