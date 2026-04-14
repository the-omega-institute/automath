import Omega.Conclusion.Window6Collision

namespace Omega.Conclusion

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the window-6 representation-zeta count ratio corollary.
    cor:conclusion-window6-representation-zeta-count-ratio -/
theorem paper_conclusion_window6_representation_zeta_count_ratio :
    (2 ^ 8 * 3 ^ 4 * 5 ^ 9 = 40500000000) ∧
    (2 ^ (8 + 4 + 9) = 2097152) ∧
    (8 + 4 + 9 = 21) ∧
    (2 ^ 21 * (3 ^ 4 * 5 ^ 9) = 2 ^ 8 * 3 ^ 4 * 5 ^ 9 * 2 ^ 13) ∧
    (cBinFiberHist 6 2 = 8 ∧ cBinFiberHist 6 3 = 4 ∧ cBinFiberHist 6 4 = 9) :=
  paper_window6_representation_zeta_count

end Omega.Conclusion
