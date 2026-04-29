import Mathlib.Tactic
import Omega.Conclusion.SingleCollapseCollisionSharpPComplete

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-qfold-choi-pdet-log-sharpp-hard`. -/
theorem paper_conclusion_qfold_choi_pdet_log_sharpp_hard
    (q N s t : ℕ) (hq : 2 ≤ q) (hsN : s ≤ N) (htN : t ≤ N) (hsEven : Even s)
    (htEven : Even t)
    (hLogPdet :
      (q - 1) * (s ^ q + (N - s)) = (q - 1) * (t ^ q + (N - t))) :
    s = t := by
  have hqsub_pos : 0 < q - 1 := by omega
  have hCollision : s ^ q + (N - s) = t ^ q + (N - t) :=
    Nat.eq_of_mul_eq_mul_left hqsub_pos hLogPdet
  exact paper_conclusion_single_collapse_collision_sharpp_complete q N s t hq hsN htN
    hsEven htEven hCollision

end Omega.Conclusion
