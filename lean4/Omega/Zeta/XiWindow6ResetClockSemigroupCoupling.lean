import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Omega.Zeta

private lemma xi_window6_reset_clock_semigroup_coupling_witness_mod21 (r : ℕ) (hr : r < 21) :
    (34 * ((13 * r) % 21)) % 21 = r := by
  interval_cases r <;> native_decide

/-- cor:xi-window6-reset-clock-semigroup-coupling -/
theorem paper_xi_window6_reset_clock_semigroup_coupling (t : ℕ) (ht : 715 ≤ t) :
    ∃ a b : ℕ, t = 34 + (21 * a + 34 * b) := by
  set n : ℕ := t - 34 with hn
  set r : ℕ := n % 21 with hr
  set b : ℕ := (13 * r) % 21 with hb
  have hr_lt : r < 21 := by
    rw [hr]
    exact Nat.mod_lt n (by decide : 0 < 21)
  have hb_lt : b < 21 := by
    rw [hb]
    exact Nat.mod_lt (13 * r) (by decide : 0 < 21)
  have hn_ge : 680 ≤ n := by
    omega
  have hb_le : 34 * b ≤ n := by
    have : b ≤ 20 := by omega
    omega
  have hb_mod : (34 * b) % 21 = n % 21 := by
    calc
      (34 * b) % 21 = r := by
        rw [hb]
        exact xi_window6_reset_clock_semigroup_coupling_witness_mod21 r hr_lt
      _ = n % 21 := by
        rw [hr]
  have hmodeq : 34 * b ≡ n [MOD 21] := by
    simpa [Nat.ModEq] using hb_mod
  have hdiv : 21 ∣ n - 34 * b := (Nat.modEq_iff_dvd' hb_le).mp hmodeq
  rcases hdiv with ⟨a, ha⟩
  refine ⟨a, b, ?_⟩
  omega

end Omega.Zeta
