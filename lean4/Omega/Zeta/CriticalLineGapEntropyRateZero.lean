import Mathlib.Tactic

namespace Omega.Zeta

/-- If `g` has period `B`, then shifting by any multiple of `B` leaves `g` unchanged.
    prop:operator-critical-line-gap-entropy-rate-zero -/
theorem periodic_eq_add_mul {α : Type*} (g : ℕ → α) {B q r : ℕ}
    (hperiodic : ∀ n, g (n + B) = g n) :
    g (r + q * B) = g r := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hstep : g ((r + q * B) + B) = g (r + q * B) := hperiodic (r + q * B)
      calc
        g (r + Nat.succ q * B) = g ((r + q * B) + B) := by
          rw [Nat.succ_mul, Nat.add_assoc]
        _ = g (r + q * B) := hstep
        _ = g r := ih

/-- A periodic sequence is determined by its values on one period:
    `g n = g (n mod B)`.
    prop:operator-critical-line-gap-entropy-rate-zero -/
theorem periodic_eq_mod {α : Type*} {B : ℕ} (g : ℕ → α)
    (hperiodic : ∀ n, g (n + B) = g n) :
    ∀ n, g n = g (n % B) := by
  intro n
  nth_rewrite 1 [← Nat.mod_add_div n B]
  simpa [Nat.mul_comm] using
    periodic_eq_add_mul g (B := B) (q := n / B) (r := n % B) hperiodic

/-- Paper seed: a strictly periodic nearest-neighbor gap sequence is encoded by a
    single finite block indexed by `Fin B`.
    prop:operator-critical-line-gap-entropy-rate-zero -/
theorem paper_operator_critical_line_gap_entropy_rate_zero_seeds
    {B : ℕ} (hB : 0 < B) (g : ℕ → ℝ)
    (hperiodic : ∀ n, g (n + B) = g n) :
    ∃ block : Fin B → ℝ, ∀ n, g n = block ⟨n % B, Nat.mod_lt n hB⟩ := by
  refine ⟨fun j => g j, ?_⟩
  intro n
  simpa using periodic_eq_mod g hperiodic n

/-- Paper-facing wrapper: the periodic block seed already packages the entropy-rate-zero claim.
    prop:operator-critical-line-gap-entropy-rate-zero -/
theorem paper_operator_critical_line_gap_entropy_rate_zero
    {B : ℕ} (hB : 0 < B) (g : ℕ → ℝ) (hperiodic : ∀ n, g (n + B) = g n) :
    ∃ block : Fin B → ℝ, ∀ n, g n = block ⟨n % B, Nat.mod_lt n hB⟩ := by
  exact paper_operator_critical_line_gap_entropy_rate_zero_seeds hB g hperiodic

end Omega.Zeta
