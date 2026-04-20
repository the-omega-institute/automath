import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GU.M11Z34RealIrrepDecomposition

namespace Omega.GU

/-- The `16` real rotation planes in the `m = 11` / `\ZZ₃₄` decomposition. -/
abbrev M11Z34RotationPlane := Fin z34RotationPlaneCount

/-- The two real coordinates inside each rotation plane. -/
abbrev M11Z34RotationCoordinate := Fin z34RotationPlaneDimension

/-- The full `32`-dimensional rotation part, packaged blockwise as `16` copies of `ℝ²`. -/
abbrev M11Z34RotationPart := M11Z34RotationPlane → M11Z34RotationCoordinate → ℝ

/-- The first coordinate in each real rotation plane. -/
abbrev m11Z34Coord0 : M11Z34RotationCoordinate := ⟨0, by decide⟩

/-- The second coordinate in each real rotation plane. -/
abbrev m11Z34Coord1 : M11Z34RotationCoordinate := ⟨1, by decide⟩

/-- Blockwise quarter-turn operator on the rotation part. -/
def m11Z34QuarterTurn (v : M11Z34RotationPart) : M11Z34RotationPart :=
  fun i j => if j = m11Z34Coord0 then -v i m11Z34Coord1 else v i m11Z34Coord0

/-- The concrete `\ZZ₃₄` action on the rotation part factors through the quarter-turn powers. -/
def m11Z34RotationAction (k : ZMod 34) (v : M11Z34RotationPart) : M11Z34RotationPart :=
  match k.val % 4 with
  | 0 => v
  | 1 => m11Z34QuarterTurn v
  | 2 => fun i j => -v i j
  | _ => fun i j => -(m11Z34QuarterTurn v i j)

private lemma m11Z34QuarterTurn_sq (v : M11Z34RotationPart) :
    m11Z34QuarterTurn (m11Z34QuarterTurn v) = fun i j => -v i j := by
  ext i j
  fin_cases j <;> simp [m11Z34QuarterTurn, m11Z34Coord0, m11Z34Coord1]

private lemma m11Z34QuarterTurn_neg (v : M11Z34RotationPart) :
    m11Z34QuarterTurn (fun i j => -v i j) = fun i j => -(m11Z34QuarterTurn v i j) := by
  ext i j
  fin_cases j <;> simp [m11Z34QuarterTurn, m11Z34Coord0, m11Z34Coord1]

private lemma m11Z34QuarterTurn_commutes_with_action (k : ZMod 34) (v : M11Z34RotationPart) :
    m11Z34QuarterTurn (m11Z34RotationAction k v) = m11Z34RotationAction k (m11Z34QuarterTurn v) := by
  have hklt : k.val % 4 < 4 := Nat.mod_lt _ (by decide)
  have hk :
      k.val % 4 = 0 ∨ k.val % 4 = 1 ∨ k.val % 4 = 2 ∨ k.val % 4 = 3 := by
    omega
  rcases hk with h0 | h1 | h2 | h3
  · simp [m11Z34RotationAction, h0]
  · simp [m11Z34RotationAction, h1, m11Z34QuarterTurn_sq]
  · simp [m11Z34RotationAction, h2, m11Z34QuarterTurn_neg]
  · simp [m11Z34RotationAction, h3, m11Z34QuarterTurn_neg, m11Z34QuarterTurn_sq]

/-- The `m = 11` / `\ZZ₃₄` rotation part is the direct sum of `16` real rotation planes, so the
blockwise quarter-turn operator defines an intrinsic complex structure and is equivariant for the
cyclic `\ZZ₃₄` action carried by those quarter-turn powers.
    cor:m11-z34-rotation-part-complex-structure -/
theorem paper_m11_z34_rotation_part_complex_structure :
    cBoundaryCount 11 = 34 ∧
      Nat.fib 9 = 34 ∧
      z34RotationPlaneCount = 16 ∧
      z34RotationPlaneDimension = 2 ∧
      z34RotationPlaneCount * z34RotationPlaneDimension = 32 ∧
      (∀ v : M11Z34RotationPart, m11Z34QuarterTurn (m11Z34QuarterTurn v) = fun i j => -v i j) ∧
      (∀ k : ZMod 34, ∀ v : M11Z34RotationPart,
        m11Z34QuarterTurn (m11Z34RotationAction k v) =
          m11Z34RotationAction k (m11Z34QuarterTurn v)) := by
  rcases paper_m11_z34_sixteen_rotation_planes_from_family_lock with
    ⟨hBoundary, hFib, _, _, _⟩
  refine ⟨hBoundary, hFib, rfl, rfl, by norm_num [z34RotationPlaneCount, z34RotationPlaneDimension], ?_, ?_⟩
  · intro v
    exact m11Z34QuarterTurn_sq v
  · intro k v
    exact m11Z34QuarterTurn_commutes_with_action k v

end Omega.GU
