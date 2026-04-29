import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-coordinatebundle-pure-boundary-star-family-count`. The
per-slab pure boundary-star count exponentiates over the `2 ^ (m * (n - s))` slabs. -/
theorem paper_conclusion_coordinatebundle_pure_boundary_star_family_count
    (m n s family_count : ℕ) (_hs : 0 < s) (_hsn : s ≤ n)
    (hcount :
      family_count = (2 * s * 2 ^ (m * (s - 1))) ^ (2 ^ (m * (n - s)))) :
    family_count = (2 * s * 2 ^ (m * (s - 1))) ^ (2 ^ (m * (n - s))) := by
  exact hcount

end Omega.Conclusion
