import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Folding.Window6

namespace Omega.Conclusion

/-- The boundary uplift sector is modeled by the regular translation action of `ZMod 6` on itself. -/
def boundaryZ6Action (g x : ZMod 6) : ZMod 6 := g + x

/-- Every pair of points in the boundary uplift sector is connected by a unique translation. -/
def boundary_uplift_is_regular_Z6_torsor : Prop :=
  ∀ x y : ZMod 6, ∃! g : ZMod 6, boundaryZ6Action g x = y

/-- The full window-`6` fiber partition is not a free finite-group orbit partition: the audited
fiber histogram has three distinct orbit sizes, and a uniform 21-orbit partition of 64 states is
arithmetically impossible. -/
def full_fiber_partition_is_not_a_free_finite_group_orbit_partition : Prop :=
  cBinFiberHist 6 2 = 8 ∧
    cBinFiberHist 6 3 = 4 ∧
    cBinFiberHist 6 4 = 9 ∧
    ¬ ∃ m : ℕ, 21 * m = 64

/-- Paper label: `thm:conclusion-window6-boundary-z6-torsor-local-global-mismatch`. -/
theorem paper_conclusion_window6_boundary_z6_torsor_local_global_mismatch :
    boundary_uplift_is_regular_Z6_torsor ∧
      full_fiber_partition_is_not_a_free_finite_group_orbit_partition := by
  refine ⟨?_, ?_⟩
  · intro x y
    refine ⟨y - x, by simp [boundaryZ6Action], ?_⟩
    intro g hg
    have hg' : g + x = y := by simpa [boundaryZ6Action] using hg
    calc
      g = g + x - x := by abel
      _ = y - x := by rw [hg']
  · refine ⟨cBinFiberHist_6_2, cBinFiberHist_6_3, cBinFiberHist_6_4, ?_⟩
    intro h
    rcases h with ⟨m, hm⟩
    omega

end Omega.Conclusion
