import Mathlib.Tactic
import Omega.CircleDimension.SolenoidFiberTorsor
import Omega.SPG.ScreenKernelConnectedComponents

namespace Omega.Conclusion

/-- The visible collision-null fiber through `x` is the preimage of the singleton `{f x}`. -/
def conclusion_collision_null_topological_torsor_visibleFiber {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : G) : Set G :=
  {y | f y = f x}

/-- Paper label: `thm:conclusion-collision-null-topological-torsor`. Any nonempty visible fiber is
an affine translate of the kernel, and the screen-kernel connected-components package gives the
rank/vanishing criterion in the connected case. -/
theorem paper_conclusion_collision_null_topological_torsor {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x y : G)
    (hy : y ∈ conclusion_collision_null_topological_torsor_visibleFiber f x)
    (c : ℕ) (hc : 0 < c) :
    Set.preimage f {f x} = conclusion_collision_null_topological_torsor_visibleFiber f x ∧
      (∃! k : G, k ∈ f.ker ∧ y = x * k) ∧
      (c - 1 = 0 ↔ c = 1) ∧
      (2 ^ (c - 1 : ℕ) = 1 ↔ c = 1) := by
  have hxy : f x = f y := by
    simpa [conclusion_collision_null_topological_torsor_visibleFiber] using hy.symm
  refine ⟨?_, Omega.CircleDimension.fiber_torsor_unique f x y hxy, ?_, ?_⟩
  · ext z
    simp [conclusion_collision_null_topological_torsor_visibleFiber]
  · exact Omega.SPG.ScreenKernelConnectedComponents.kernel_dim_eq_components_minus_one c hc
  · exact Omega.SPG.ScreenKernelConnectedComponents.fiber_card_binary c (Nat.succ_le_of_lt hc)

end Omega.Conclusion
