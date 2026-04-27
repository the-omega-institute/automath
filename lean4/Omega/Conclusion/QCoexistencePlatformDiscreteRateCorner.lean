import Omega.Conclusion.DiscreteConvexBudgetKinkFan

namespace Omega.Conclusion

open Set

lemma paper_conclusion_q_coexistence_platform_discrete_rate_corner_slope_mono
    (Q : ℕ) (Phi : ℕ → ℝ)
    (hconv : ∀ r : ℕ, 2 < r → r < Q →
      Phi r - Phi (r - 1) ≤ Phi (r + 1) - Phi r) :
    MonotoneOn (fun r : ℕ => Phi r - Phi (r - 1)) (Icc 3 Q) := by
  refine monotoneOn_of_le_succ ordConnected_Icc ?_
  intro r _ hr hsucc
  have hrTwo : 2 < r := lt_of_lt_of_le (by decide : 2 < 3) hr.1
  have hrQ : r < Q := Nat.lt_of_succ_le hsucc.2
  simpa [Nat.succ_eq_add_one] using hconv r hrTwo hrQ

lemma paper_conclusion_q_coexistence_platform_discrete_rate_corner_lower_bound
    (Q qlo : ℕ) (Phi : ℕ → ℝ) (gamma : ℝ) (hlo : 2 < qlo)
    (hloMax : ∀ r : ℕ, 2 ≤ r → r ≤ Q →
      ((r - 1 : ℝ) * gamma - Phi r) ≤ ((qlo - 1 : ℝ) * gamma - Phi qlo))
    (m : ℕ) (hmlo : qlo ≤ m) (hmQ : m ≤ Q) :
    Phi qlo + (m - qlo : ℝ) * gamma ≤ Phi m := by
  have hmTwo : 2 ≤ m := le_trans (le_of_lt hlo) hmlo
  have hmax := hloMax m hmTwo hmQ
  have hcast : (m - 1 : ℝ) = (qlo - 1 : ℝ) + (m - qlo : ℝ) := by
    ring_nf
  rw [hcast] at hmax
  linarith

/-- Paper label: `thm:conclusion-q-coexistence-platform-discrete-rate-corner`. -/
theorem paper_conclusion_q_coexistence_platform_discrete_rate_corner
    (Q qlo qhi : Nat) (Phi : Nat -> Real) (gamma : Real) (hlo : 2 < qlo)
    (hhi : qhi < Q) (hle : qlo <= qhi)
    (hconv : forall r : Nat, 2 < r -> r < Q ->
      Phi r - Phi (r - 1) <= Phi (r + 1) - Phi r)
    (hloMax : forall r : Nat, 2 <= r -> r <= Q ->
      ((r - 1 : Real) * gamma - Phi r) <= ((qlo - 1 : Real) * gamma - Phi qlo))
    (hhiMax : forall r : Nat, 2 <= r -> r <= Q ->
      ((r - 1 : Real) * gamma - Phi r) <= ((qhi - 1 : Real) * gamma - Phi qhi)) :
    forall n : Nat, qlo <= n -> n <= qhi ->
      Phi n = Phi qlo + (n - qlo : Real) * gamma := by
  have hqhiTwo : 2 < qhi := lt_of_lt_of_le hlo hle
  have hqloQ : qlo < Q := lt_of_le_of_lt hle hhi
  have hSlopeMono :
      MonotoneOn (fun r : ℕ => Phi r - Phi (r - 1)) (Icc 3 Q) :=
    paper_conclusion_q_coexistence_platform_discrete_rate_corner_slope_mono Q Phi hconv
  have hQhiMaxSlope :
      Phi qhi - Phi (qhi - 1) ≤ gamma := by
    exact
      (paper_conclusion_discrete_convex_budget_kink_fan Q qhi Phi gamma hqhiTwo hhi
        hconv).mp hhiMax |>.1
  have hSlopeLeGamma :
      ∀ a : ℕ, qlo ≤ a → a < qhi → Phi (a + 1) - Phi a ≤ gamma := by
    intro a haqlo haqhi
    have haSuccLe : a + 1 ≤ qhi := Nat.succ_le_of_lt haqhi
    have haSuccMem : a + 1 ∈ Icc 3 Q := by
      constructor
      · omega
      · exact le_trans haSuccLe hhi.le
    have hqhiMem : qhi ∈ Icc 3 Q := by
      exact ⟨Nat.succ_le_of_lt hqhiTwo, hhi.le⟩
    have hmono := hSlopeMono haSuccMem hqhiMem haSuccLe
    have hstep : Phi (a + 1) - Phi a ≤ Phi qhi - Phi (qhi - 1) := by
      simpa using hmono
    exact hstep.trans hQhiMaxSlope
  have hLower :
      ∀ m : ℕ, qlo ≤ m → m ≤ qhi → Phi qlo + (m - qlo : ℝ) * gamma ≤ Phi m := by
    intro m hmlo hmhi
    exact paper_conclusion_q_coexistence_platform_discrete_rate_corner_lower_bound Q qlo
      Phi gamma hlo hloMax m hmlo (le_trans hmhi hhi.le)
  intro n hnlo hnhi
  have hByDistance :
      ∀ d : ℕ, qlo + d ≤ qhi →
        Phi (qlo + d) = Phi qlo + (d : ℝ) * gamma := by
    intro d
    induction d with
    | zero =>
        intro _
        simp
    | succ d ih =>
        intro hdle
        have hprevLe : qlo + d ≤ qhi := le_trans (Nat.le_succ (qlo + d)) hdle
        have hprev := ih hprevLe
        have hlt : qlo + d < qhi := by omega
        have hstep : Phi (qlo + Nat.succ d) - Phi (qlo + d) ≤ gamma := by
          have := hSlopeLeGamma (qlo + d) (by omega) hlt
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using this
        have hupper : Phi (qlo + Nat.succ d) ≤ Phi qlo + (Nat.succ d : ℝ) * gamma := by
          calc
            Phi (qlo + Nat.succ d) ≤ Phi (qlo + d) + gamma := by linarith
            _ = Phi qlo + (d : ℝ) * gamma + gamma := by rw [hprev]
            _ = Phi qlo + (Nat.succ d : ℝ) * gamma := by
              rw [Nat.cast_succ]
              ring
        have hlower :
            Phi qlo + (Nat.succ d : ℝ) * gamma ≤ Phi (qlo + Nat.succ d) := by
          have := hLower (qlo + Nat.succ d) (by omega) hdle
          simpa [Nat.succ_eq_add_one, Nat.add_assoc] using this
        exact le_antisymm hupper hlower
  have hnEq : n = qlo + (n - qlo) := by omega
  calc
    Phi n = Phi (qlo + (n - qlo)) := congrArg Phi hnEq
    _ = Phi qlo + ((n - qlo : ℕ) : ℝ) * gamma := hByDistance (n - qlo) (by omega)
    _ = Phi qlo + (n - qlo : ℝ) * gamma := by rw [Nat.cast_sub hnlo]

end Omega.Conclusion
