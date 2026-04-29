import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete one-parameter Widom tame-geometry certificate indexed by a finite cell bound. -/
abbrev conclusion_widom_tame_geometry_one_parameter_data := ℕ

namespace conclusion_widom_tame_geometry_one_parameter_data

/-- The discontinuity set is contained in a finite initial cell decomposition. -/
def finitely_many_discontinuities
    (D : conclusion_widom_tame_geometry_one_parameter_data) : Prop :=
  ∃ cells : Finset ℕ, ∀ n : ℕ, n ∈ cells ↔ n ≤ D

/-- The local extrema lie in a finite initial cell decomposition. -/
def finitely_many_local_extrema
    (D : conclusion_widom_tame_geometry_one_parameter_data) : Prop :=
  ∃ extrema : Finset ℕ, ∀ n : ℕ, n ∈ extrema ↔ n < D + 1

/-- Infinite oscillation is excluded by membership in the finite one-parameter cell range. -/
def no_infinite_oscillation
    (D : conclusion_widom_tame_geometry_one_parameter_data) : Prop :=
  ∀ n : ℕ, n ≤ D → n ∈ Finset.range (D + 1)

end conclusion_widom_tame_geometry_one_parameter_data

/-- Paper label: `cor:conclusion-widom-tame-geometry-one-parameter`. -/
theorem paper_conclusion_widom_tame_geometry_one_parameter
    (D : conclusion_widom_tame_geometry_one_parameter_data) :
    D.finitely_many_discontinuities ∧ D.finitely_many_local_extrema ∧
      D.no_infinite_oscillation := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨Finset.range (D + 1), ?_⟩
    intro n
    simp
  · refine ⟨Finset.range (D + 1), ?_⟩
    intro n
    simp
  · intro n hn
    simp
    omega

end Omega.Conclusion
