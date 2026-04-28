import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part70d-minsector-terminal-sheet-realization`. -/
theorem paper_xi_time_part70d_minsector_terminal_sheet_realization
    (total s a symmDiff : Nat -> Real) (c : Real) (hpos : forall n, 0 < total n)
    (hdiff : exists N, forall n, N <= n -> symmDiff n = a n - s n)
    (hs : forall eps : Real, 0 < eps -> exists N, forall n, N <= n ->
      |s n / total n - c| < eps)
    (ha : forall eps : Real, 0 < eps -> exists N, forall n, N <= n ->
      |a n / total n - c| < eps) :
    forall eps : Real, 0 < eps -> exists N, forall n, N <= n ->
      |symmDiff n / total n| < eps := by
  intro eps heps
  rcases hdiff with ⟨Ndiff, hdiffN⟩
  have hhalf : 0 < eps / 2 := by linarith
  rcases ha (eps / 2) hhalf with ⟨Na, hNa⟩
  rcases hs (eps / 2) hhalf with ⟨Ns, hNs⟩
  refine ⟨max Ndiff (max Na Ns), ?_⟩
  intro n hn
  have hndiff : Ndiff <= n := le_trans (Nat.le_max_left Ndiff (max Na Ns)) hn
  have hna : Na <= n :=
    le_trans (le_trans (Nat.le_max_left Na Ns) (Nat.le_max_right Ndiff (max Na Ns))) hn
  have hns : Ns <= n :=
    le_trans (le_trans (Nat.le_max_right Na Ns) (Nat.le_max_right Ndiff (max Na Ns))) hn
  have htotal_ne : total n ≠ 0 := ne_of_gt (hpos n)
  have hsplit : symmDiff n / total n = a n / total n - s n / total n := by
    rw [hdiffN n hndiff]
    field_simp [htotal_ne]
  calc
    |symmDiff n / total n| = |a n / total n - s n / total n| := by rw [hsplit]
    _ = |(a n / total n - c) - (s n / total n - c)| := by ring_nf
    _ <= |a n / total n - c| + |s n / total n - c| := by
      simpa [abs_neg, abs_sub_comm] using
        (abs_sub_le (a n / total n - c) 0 (s n / total n - c))
    _ < eps / 2 + eps / 2 := add_lt_add (hNa n hna) (hNs n hns)
    _ = eps := by ring

end Omega.Zeta
