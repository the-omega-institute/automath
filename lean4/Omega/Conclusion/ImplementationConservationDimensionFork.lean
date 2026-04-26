import Omega.CircleDimension.ImplementationStructuralHalfCircleDimension

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-implementation-conservation-dimension-fork`. -/
theorem paper_conclusion_implementation_conservation_dimension_fork :
    Function.Injective
        Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_embedding ∧
      Omega.CircleDimension.killo_implementation_vs_structural_half_circle_dimension_impl_dim =
        (1 : ℚ) / 2 ∧
      (∀ k : ℕ, Omega.Folding.killoFiniteRegisterLinearizationObstructed k) := by
  rcases Omega.CircleDimension.paper_killo_implementation_vs_structural_half_circle_dimension with
    ⟨_, hobstructed, hinjective, himpl_dim⟩
  exact ⟨hinjective, himpl_dim, hobstructed⟩

end Omega.Conclusion
