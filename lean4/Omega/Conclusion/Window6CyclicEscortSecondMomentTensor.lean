import Mathlib.Tactic

namespace Omega.Conclusion

/-- Integer coordinate root used for the window-6 cyclic root cloud. -/
abbrev conclusion_window6_cyclic_escort_second_moment_tensor_root := ℤ × ℤ × ℤ

/-- Coordinate-square sum of a finite root stratum. -/
def conclusion_window6_cyclic_escort_second_moment_tensor_squareSum
    (roots : List conclusion_window6_cyclic_escort_second_moment_tensor_root) :
    ℤ × ℤ × ℤ :=
  roots.foldl
    (fun acc r => (acc.1 + r.1 ^ 2, acc.2.1 + r.2.1 ^ 2, acc.2.2 + r.2.2 ^ 2))
    (0, 0, 0)

/-- Degeneracy-four stratum
`{e₁, ±e₂, ±e₃} ∪ {(±1, ±1, 0)}`. -/
def conclusion_window6_cyclic_escort_second_moment_tensor_phi4 :
    List conclusion_window6_cyclic_escort_second_moment_tensor_root :=
  [(1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1),
    (1, 1, 0), (1, -1, 0), (-1, 1, 0), (-1, -1, 0)]

/-- Degeneracy-three stratum `{(±1, 0, ±1)}`. -/
def conclusion_window6_cyclic_escort_second_moment_tensor_phi3 :
    List conclusion_window6_cyclic_escort_second_moment_tensor_root :=
  [(1, 0, 1), (1, 0, -1), (-1, 0, 1), (-1, 0, -1)]

/-- Degeneracy-two stratum `{-e₁} ∪ {(0, ±1, ±1)}`. -/
def conclusion_window6_cyclic_escort_second_moment_tensor_phi2 :
    List conclusion_window6_cyclic_escort_second_moment_tensor_root :=
  [(-1, 0, 0), (0, 1, 1), (0, 1, -1), (0, -1, 1), (0, -1, -1)]

/-- The diagonal second-moment tensor encoded by its three diagonal entries. -/
def conclusion_window6_cyclic_escort_second_moment_tensor (q : ℕ) : ℤ × ℤ × ℤ :=
  ((4 : ℤ) ^ q * 5 + (3 : ℤ) ^ q * 4 + (2 : ℤ) ^ q,
    (4 : ℤ) ^ q * 6 + (2 : ℤ) ^ q * 4,
    (4 : ℤ) ^ q * 2 + (3 : ℤ) ^ q * 4 + (2 : ℤ) ^ q * 4)

/-- Paper label: `thm:conclusion-window6-cyclic-escort-second-moment-tensor`. -/
theorem paper_conclusion_window6_cyclic_escort_second_moment_tensor (q : ℕ) :
    conclusion_window6_cyclic_escort_second_moment_tensor_squareSum
        conclusion_window6_cyclic_escort_second_moment_tensor_phi4 = (5, 6, 2) ∧
      conclusion_window6_cyclic_escort_second_moment_tensor_squareSum
        conclusion_window6_cyclic_escort_second_moment_tensor_phi3 = (4, 0, 4) ∧
      conclusion_window6_cyclic_escort_second_moment_tensor_squareSum
        conclusion_window6_cyclic_escort_second_moment_tensor_phi2 = (1, 4, 4) ∧
      conclusion_window6_cyclic_escort_second_moment_tensor q =
        ((4 : ℤ) ^ q * 5 + (3 : ℤ) ^ q * 4 + (2 : ℤ) ^ q,
          (4 : ℤ) ^ q * 6 + (2 : ℤ) ^ q * 4,
          (4 : ℤ) ^ q * 2 + (3 : ℤ) ^ q * 4 + (2 : ℤ) ^ q * 4) ∧
      conclusion_window6_cyclic_escort_second_moment_tensor 0 = (10, 10, 10) ∧
      conclusion_window6_cyclic_escort_second_moment_tensor 1 = (34, 32, 28) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_window6_cyclic_escort_second_moment_tensor_squareSum,
      conclusion_window6_cyclic_escort_second_moment_tensor_phi4]
  · norm_num [conclusion_window6_cyclic_escort_second_moment_tensor_squareSum,
      conclusion_window6_cyclic_escort_second_moment_tensor_phi3]
  · norm_num [conclusion_window6_cyclic_escort_second_moment_tensor_squareSum,
      conclusion_window6_cyclic_escort_second_moment_tensor_phi2]
  · rfl
  · norm_num [conclusion_window6_cyclic_escort_second_moment_tensor]
  · norm_num [conclusion_window6_cyclic_escort_second_moment_tensor]

end Omega.Conclusion
