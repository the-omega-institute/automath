import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part57ea-oracle-capacity-defect-top-formula`. -/
theorem paper_xi_time_part57ea_oracle_capacity_defect_top_formula {X : Type*} [Fintype X]
    (d : X → ℕ) (T M total K : ℕ) (hT : T ≤ M)
    (hlarge : ∀ x, d x = M ∨ d x ≤ T)
    (hcount : (Finset.univ.filter (fun x => d x = M)).card = K)
    (htotal : (∑ x, d x) = total) :
    (∑ x, Nat.min (d x) T) = total - K * (M - T) := by
  classical
  have hpoint :
      ∀ x, Nat.min (d x) T + (if d x = M then M - T else 0) = d x := by
    intro x
    by_cases hx : d x = M
    · rw [if_pos hx, hx]
      have hmin : M.min T = T := Nat.min_eq_right hT
      rw [hmin]
      omega
    · rw [if_neg hx]
      rcases hlarge x with hM | hle
      · exact False.elim (hx hM)
      · have hmin : (d x).min T = d x := Nat.min_eq_left hle
        rw [hmin]
        omega
  have hdefect :
      (∑ x, if d x = M then M - T else 0) = K * (M - T) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, hcount]
    simp
  have hsum :
      (∑ x, Nat.min (d x) T) + K * (M - T) = total := by
    calc
      (∑ x, Nat.min (d x) T) + K * (M - T)
          = (∑ x, Nat.min (d x) T) + ∑ x, if d x = M then M - T else 0 := by
              rw [hdefect]
      _ = ∑ x, (Nat.min (d x) T + if d x = M then M - T else 0) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ x, d x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              exact hpoint x
      _ = total := htotal
  omega

end Omega.Zeta
