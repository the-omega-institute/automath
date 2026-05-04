import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-window6-edge-separation-antipodal-residue`. -/
theorem paper_conclusion_window6_edge_separation_antipodal_residue
    (E N : Nat -> Nat) (hpair : ∀ k, 1 ≤ k -> k ≤ 6 -> 2 * E k = N k)
    (hN1 : N 1 = 0) (hN2 : N 2 = 32) (hN3 : N 3 = 32) (hN4 : N 4 = 56)
    (hN5 : N 5 = 24) (hN6 : N 6 = 4) :
    E 1 = 0 ∧ E 2 = 16 ∧ E 3 = 16 ∧ E 4 = 28 ∧ E 5 = 12 ∧ E 6 = 2 := by
  have h1 := hpair 1 (by norm_num) (by norm_num)
  have h2 := hpair 2 (by norm_num) (by norm_num)
  have h3 := hpair 3 (by norm_num) (by norm_num)
  have h4 := hpair 4 (by norm_num) (by norm_num)
  have h5 := hpair 5 (by norm_num) (by norm_num)
  have h6 := hpair 6 (by norm_num) (by norm_num)
  omega

end Omega.Conclusion
