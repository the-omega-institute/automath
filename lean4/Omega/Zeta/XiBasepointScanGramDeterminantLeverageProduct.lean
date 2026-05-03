import Mathlib

namespace Omega.Zeta

/-- Paper label: `cor:xi-basepoint-scan-gram-determinant-leverage-product`. -/
theorem paper_xi_basepoint_scan_gram_determinant_leverage_product (det leverage : ℕ → ℝ)
    (n : ℕ) (h0 : det 0 = 1)
    (hstep : ∀ m < n, det (m + 1) = det m * leverage (m + 1)) :
    det n = (List.range n).foldl (fun acc m => acc * leverage (m + 1)) 1 := by
  revert hstep
  induction n with
  | zero =>
      intro hstep
      simp [h0]
  | succ n ih =>
      intro hstep
      have hprev :
          det n = (List.range n).foldl (fun acc m => acc * leverage (m + 1)) 1 := by
        exact ih (fun m hm => hstep m (Nat.lt_trans hm (Nat.lt_succ_self n)))
      have hlast : det (n + 1) = det n * leverage (n + 1) :=
        hstep n (Nat.lt_succ_self n)
      rw [hlast, hprev]
      simp [List.range_succ, List.foldl_append]

end Omega.Zeta
