import Omega.Folding.BoundaryLayer

namespace Omega.GroupUnification

/-- Paper label: `thm:bdry-three-window-sum12-unique-even-triple`. -/
theorem paper_bdry_three_window_sum12_unique_even_triple
    (m1 m2 m3 : Nat) (hm1_even : Even m1) (hm2_even : Even m2) (hm3_even : Even m3)
    (h12 : m1 < m2) (h23 : m2 < m3) (hm1_pos : 2 <= m1)
    (hsum : Nat.fib (m1 - 2) + Nat.fib (m2 - 2) + Nat.fib (m3 - 2) = 12) :
    m1 = 4 ∧ m2 = 6 ∧ m3 = 8 := by
  exact Omega.bdry_three_window_sum12_unique m1 m2 m3 hm1_even hm2_even hm3_even
    h12 h23 hm1_pos hsum

end Omega.GroupUnification
