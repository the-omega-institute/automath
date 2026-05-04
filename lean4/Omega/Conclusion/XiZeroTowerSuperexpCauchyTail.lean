import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-xi-zero-tower-superexp-cauchy-tail`. -/
theorem paper_conclusion_xi_zero_tower_superexp_cauchy_tail
    (tau E : ℕ → ℝ) (C r : ℝ) (K : ℕ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hE0 : ∀ j, K ≤ j → 0 ≤ E j)
    (hE : ∀ j, K ≤ j → E (j + 1) ≤ r * E j)
    (hstep : ∀ j, K ≤ j → |tau (j + 1) - tau j| ≤ C * E j) :
    ∀ j, K ≤ j → |tau (j + 1) - tau j| ≤ C * E K * r ^ (j - K) := by
  have _hr1 : r < 1 := hr1
  have _hEK_nonneg : 0 ≤ E K := hE0 K (le_rfl)
  have hgeom : ∀ n : ℕ, E (K + n) ≤ E K * r ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hKle : K ≤ K + n := Nat.le_add_right K n
        have hnext : E (K + n + 1) ≤ r * E (K + n) := hE (K + n) hKle
        have hmul : r * E (K + n) ≤ r * (E K * r ^ n) :=
          mul_le_mul_of_nonneg_left ih hr0
        calc
          E (K + Nat.succ n) = E (K + n + 1) := by rw [Nat.add_succ]
          _ ≤ r * E (K + n) := hnext
          _ ≤ r * (E K * r ^ n) := hmul
          _ = E K * r ^ Nat.succ n := by
            rw [pow_succ]
            ring
  intro j hj
  have hEj : E j ≤ E K * r ^ (j - K) := by
    simpa [Nat.add_sub_of_le hj] using hgeom (j - K)
  have hscaled : C * E j ≤ C * (E K * r ^ (j - K)) :=
    mul_le_mul_of_nonneg_left hEj hC
  calc
    |tau (j + 1) - tau j| ≤ C * E j := hstep j hj
    _ ≤ C * (E K * r ^ (j - K)) := hscaled
    _ = C * E K * r ^ (j - K) := by ring

end Omega.Conclusion
