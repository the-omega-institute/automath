import Mathlib.Tactic
import Omega.Zeta.XiWindow6TailSemigroupAperyThresholds

namespace Omega.Zeta

private lemma tail_three_generator_iff_two_generator (n : ℕ) :
    (∃ a b c : ℕ, n = 21 * a + 34 * b + 55 * c) ↔ ∃ a b : ℕ, n = 21 * a + 34 * b := by
  constructor
  · rintro ⟨a, b, c, h⟩
    refine ⟨a + c, b + c, ?_⟩
    omega
  · rintro ⟨a, b, h⟩
    exact ⟨a, b, 0, by simpa using h⟩

/-- Since `55 = 21 + 34`, the window-6 tail semigroup is already the numerical semigroup
`⟨21, 34⟩`; its conductor is therefore `660` and `659` is the last missing value.
    thm:xi-window6-tail-semigroup-frobenius-threshold -/
theorem paper_xi_window6_tail_semigroup_frobenius_threshold :
    (∀ n : ℕ, 660 ≤ n → ∃ a b c : ℕ, n = 21 * a + 34 * b + 55 * c) ∧
    ¬ ∃ a b c : ℕ, 659 = 21 * a + 34 * b + 55 * c := by
  refine ⟨?_, ?_⟩
  · intro n hn
    let b : ℕ := (13 * (n % 21)) % 21
    have hthreshold : 34 * b ≤ n := by
      dsimp [b]
      have hlt : n % 21 < 21 := Nat.mod_lt n (by decide)
      interval_cases h : n % 21 <;> omega
    have hrepr : ∃! a : ℕ, n = 21 * a + 34 * b := by
      simpa [b] using
        (paper_xi_window6_tail_semigroup_two_generator_normal_form n).mp hthreshold
    rcases hrepr with ⟨a, ha, _⟩
    exact ⟨a, b, 0, by omega⟩
  · intro h
    have hno_two :
        ¬ ∃ a b : ℕ, 659 = 21 * a + 34 * b := by
      have hresidue :
          ∀ r : Fin 21, ∀ n : ℕ, n % 21 = r.1 →
            ((∃ a c : ℕ, n = 21 * a + 34 * c) ↔ 34 * ((13 * r.1) % 21) ≤ n) := by
        simpa using paper_xi_window6_tail_semigroup_apery_thresholds.1
      have hmain : (∃ a b : ℕ, 659 = 21 * a + 34 * b) ↔ 680 ≤ 659 := by
        simpa using hresidue ⟨8, by decide⟩ 659 (by native_decide : 659 % 21 = 8)
      have hfalse : ¬ 680 ≤ 659 := by decide
      exact fun hrep => hfalse (hmain.mp hrep)
    exact hno_two ((tail_three_generator_iff_two_generator 659).mp h)

end Omega.Zeta
