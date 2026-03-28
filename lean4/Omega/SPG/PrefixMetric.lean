import Mathlib.Topology.MetricSpace.PiNat
import Omega.SPG.Cylinder

namespace Omega.SPG

open PiNat

/-- The standard prefix ultrametric on `OmegaInfinity`, reused from `PiNat.dist`. -/
noncomputable def prefixDist (x y : OmegaInfinity) : ℝ :=
  @Dist.dist OmegaInfinity PiNat.dist x y

@[simp] theorem prefixDist_def (x y : OmegaInfinity) :
    prefixDist x y = @Dist.dist OmegaInfinity PiNat.dist x y := rfl

/-- The depth-`m` prefix ball around `x` is exactly the cylinder determined by the first `m` bits. -/
def prefixBall (x : OmegaInfinity) (m : Nat) : Set OmegaInfinity :=
  PiNat.cylinder x m

@[simp] theorem mem_prefixBall_iff (x y : OmegaInfinity) (m : Nat) :
    y ∈ prefixBall x m ↔ prefixWord y m = prefixWord x m := by
  constructor
  · intro hy
    funext i
    exact hy i.1 i.2
  · intro hy i hi
    have := congrFun hy ⟨i, hi⟩
    simpa [prefixWord] using this

theorem prefixBall_eq_cylinderWord (x : OmegaInfinity) (m : Nat) :
    prefixBall x m = cylinderWord (prefixWord x m) := by
  ext y
  simp [mem_prefixBall_iff, cylinderWord]

theorem cylinderWord_eq_closedBall (w : Word m) :
    cylinderWord w = {x : OmegaInfinity | prefixDist x (extendWord w) ≤ (1 / 2 : ℝ) ^ m} := by
  rw [cylinderWord_eq_piCylinder]
  ext x
  simpa [prefixDist, PiNat.dist_comm] using
    (PiNat.mem_cylinder_iff_dist_le (x := extendWord w) (y := x) (n := m))

theorem prefixBall_eq_closedBall (x : OmegaInfinity) (m : Nat) :
    prefixBall x m = {y : OmegaInfinity | prefixDist y x ≤ (1 / 2 : ℝ) ^ m} := by
  ext y
  simpa [prefixBall, prefixDist] using
    (PiNat.mem_cylinder_iff_dist_le (x := x) (y := y) (n := m))

theorem prefixBall_anti (x : OmegaInfinity) {m n : Nat} (h : m ≤ n) :
    prefixBall x n ⊆ prefixBall x m :=
  PiNat.cylinder_anti x h

/-- Prefix balls are nested: higher resolution gives smaller balls. -/
theorem prefixBall_nested (x : OmegaInfinity) (m : Nat) :
    prefixBall x (m + 1) ⊆ prefixBall x m :=
  prefixBall_anti x (Nat.le_succ m)

/-- Every point is in its own prefix ball. -/
theorem mem_prefixBall_self (x : OmegaInfinity) (m : Nat) :
    x ∈ prefixBall x m := by
  simp [prefixBall, PiNat.mem_cylinder_iff]


end Omega.SPG
