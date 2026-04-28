import Mathlib.Topology.Basic

namespace Omega.Conclusion

/-- Every relative neighborhood contains two certified points with different local dimensions. -/
def conclusion_zg_local_dimension_nowhere_continuous_oscillation
    {X A : Type*} [TopologicalSpace X] (D : Set X) (d : D → A) : Prop :=
  ∀ x : D, ∀ U : Set X, IsOpen U → (x : X) ∈ U →
    ∃ y z : D, (y : X) ∈ U ∧ (z : X) ∈ U ∧ d y ≠ d z

/-- The local-dimension observable is nowhere locally constant on its relative domain. -/
def conclusion_zg_local_dimension_nowhere_continuous_nowhereContinuousOn
    {X A : Type*} [TopologicalSpace X] (D : Set X) (d : D → A) : Prop :=
  ∀ x : D, ∀ U : Set X, IsOpen U → (x : X) ∈ U →
    ∃ y : D, (y : X) ∈ U ∧ d y ≠ d x

/-- Paper label: `prop:conclusion-zg-local-dimension-nowhere-continuous`. -/
theorem paper_conclusion_zg_local_dimension_nowhere_continuous
    {X A : Type*} [TopologicalSpace X] (D : Set X) (d : D → A)
    (h : conclusion_zg_local_dimension_nowhere_continuous_oscillation D d) :
    conclusion_zg_local_dimension_nowhere_continuous_nowhereContinuousOn D d := by
  intro x U hU hxU
  rcases h x U hU hxU with ⟨y, z, hyU, hzU, hyz⟩
  by_cases hyx : d y = d x
  · refine ⟨z, hzU, ?_⟩
    intro hzx
    exact hyz (hyx.trans hzx.symm)
  · exact ⟨y, hyU, hyx⟩

end Omega.Conclusion
