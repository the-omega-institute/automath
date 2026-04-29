import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-coordinate-bundle-fourfold-complexity-collapse`. -/
theorem paper_conclusion_coordinate_bundle_fourfold_complexity_collapse
    (m n s LJ shannon audit linear : ℕ)
    (kolmogorov : ℤ) (hLJ : LJ = 2 ^ (m * (n - s))) (hshannon : shannon = LJ)
    (haudit : audit = LJ) (hlinear : linear = LJ) (hkol : kolmogorov = LJ) :
    shannon = 2 ^ (m * (n - s)) ∧ audit = 2 ^ (m * (n - s)) ∧
      linear = 2 ^ (m * (n - s)) ∧ kolmogorov = 2 ^ (m * (n - s)) := by
  subst shannon
  subst audit
  subst linear
  subst kolmogorov
  subst LJ
  simp

end Omega.Conclusion
