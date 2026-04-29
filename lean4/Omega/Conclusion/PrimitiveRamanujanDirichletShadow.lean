import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-primitive-ramanujan-dirichlet-shadow`. -/
theorem paper_conclusion_primitive_ramanujan_dirichlet_shadow {R : Type*} [Semiring R]
    (DirichletShadow RamanujanWeighted WittMobiusWeighted : ℕ → R)
    (hDirichlet : ∀ n, DirichletShadow n = RamanujanWeighted n)
    (hWitt : ∀ n, RamanujanWeighted n = WittMobiusWeighted n) :
    (∀ n, DirichletShadow n = RamanujanWeighted n) ∧
      (∀ n, DirichletShadow n = WittMobiusWeighted n) := by
  refine ⟨hDirichlet, ?_⟩
  intro n
  rw [hDirichlet n, hWitt n]

end Omega.Conclusion
