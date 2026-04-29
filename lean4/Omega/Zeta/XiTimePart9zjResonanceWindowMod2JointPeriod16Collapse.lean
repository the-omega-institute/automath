import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9zj-resonance-window-mod2-joint-period16-collapse`. -/
lemma xi_time_part9zj_resonance_window_mod2_joint_period16_collapse_iterate
    (T : Nat → Bool) (p k m : Nat) (hperiodic : ∀ n, T (n + p) = T n) :
    T (m + p * k) = T m := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hperiodic, ih]

/-- Paper label: `thm:xi-time-part9zj-resonance-window-mod2-joint-period16-collapse`. -/
theorem paper_xi_time_part9zj_resonance_window_mod2_joint_period16_collapse
    (S : Fin 9 → Nat → Bool) (period : Fin 9 → Nat) (hpos : ∀ i, 0 < period i)
    (hdvd : ∀ i, period i ∣ 16) (hperiodic : ∀ i m, S i (m + period i) = S i m) :
    ∀ m, (fun i => S i (m + 16)) = fun i => S i m := by
  intro m
  funext i
  have _hperiod_pos : 0 < period i := hpos i
  obtain ⟨k, hk⟩ := hdvd i
  rw [hk]
  exact xi_time_part9zj_resonance_window_mod2_joint_period16_collapse_iterate
    (S i) (period i) k m (hperiodic i)

end Omega.Zeta
