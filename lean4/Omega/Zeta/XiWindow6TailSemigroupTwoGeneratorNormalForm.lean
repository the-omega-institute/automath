import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Omega.Zeta

private lemma window6_tail_witness_mod21 (r : ℕ) (hr : r < 21) :
    (34 * ((13 * r) % 21)) % 21 = r := by
  interval_cases r <;> native_decide

/-- The `{21, 34, 55}` tail semigroup already reduces to the two generators `{21, 34}` because
`55 = 21 + 34`; reducing `n` modulo `21` fixes the unique canonical `34`-coefficient
`b = (13 * (n % 21)) % 21`, and reachability is exactly the threshold condition `n ≥ 34 * b`.
    thm:xi-window6-tail-semigroup-two-generator-normal-form -/
theorem paper_xi_window6_tail_semigroup_two_generator_normal_form (n : ℕ) :
    let r := n % 21
    let b := (13 * r) % 21
    let w := 34 * b
    (n ≥ w ↔ ∃! a : ℕ, n = 21 * a + 34 * b) := by
  dsimp
  set r : ℕ := n % 21 with hr
  set b : ℕ := (13 * r) % 21 with hb
  set w : ℕ := 34 * b with hw
  have hr_lt : r < 21 := by
    rw [hr]
    exact Nat.mod_lt n (by decide : 0 < 21)
  have hw_mod : w % 21 = n % 21 := by
    calc
      w % 21 = r := by
        rw [hw, hb]
        exact window6_tail_witness_mod21 r hr_lt
      _ = n % 21 := by
        rw [hr]
  constructor
  · intro hnw
    have hmodeq : w ≡ n [MOD 21] := by
      simpa [Nat.ModEq] using hw_mod
    have hdiv : 21 ∣ n - w := (Nat.modEq_iff_dvd' hnw).mp hmodeq
    rcases hdiv with ⟨a, ha⟩
    refine ⟨a, ?_, ?_⟩
    · omega
    · intro a' ha'
      omega
  · rintro ⟨a, ha, _⟩
    omega

end Omega.Zeta
