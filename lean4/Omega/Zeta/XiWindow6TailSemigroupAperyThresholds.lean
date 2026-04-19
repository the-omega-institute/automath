import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.Zeta.XiWindow6TailSemigroupTwoGeneratorNormalForm

namespace Omega.Zeta

/-- The Apéry thresholds of the numerical semigroup `⟨21,34⟩` are read off from the canonical
two-generator normal form residue by residue; the corresponding congruence-class gap counts sum
to `330`.
    prop:xi-window6-tail-semigroup-apery-thresholds -/
theorem paper_xi_window6_tail_semigroup_apery_thresholds :
    let b : Fin 21 → ℕ := fun r => (13 * r.1) % 21
    let w : Fin 21 → ℕ := fun r => 34 * b r
    let g : Fin 21 → ℕ := fun r => (w r - r.1) / 21
    (∀ r : Fin 21, ∀ n : ℕ, n % 21 = r.1 →
      ((∃ a c : ℕ, n = 21 * a + 34 * c) ↔ w r ≤ n)) ∧
      (∑ r : Fin 21, g r = 330) := by
  dsimp
  refine ⟨?_, ?_⟩
  · intro r n hr
    let b : ℕ := (13 * r.1) % 21
    have hcanon :
        ((∃ a c : ℕ, n = 21 * a + 34 * c) ↔ ∃ a : ℕ, n = 21 * a + 34 * b) := by
      constructor
      · rintro ⟨a, c, h⟩
        have hc_mod : c % 21 = b := by
          dsimp [b]
          omega
        refine ⟨a + 34 * (c / 21), ?_⟩
        have hc : c = 21 * (c / 21) + b := by
          calc
            c = c % 21 + 21 * (c / 21) := by
              symm
              exact Nat.mod_add_div c 21
            _ = b + 21 * (c / 21) := by rw [hc_mod]
            _ = 21 * (c / 21) + b := by omega
        omega
      · rintro ⟨a, ha⟩
        exact ⟨a, b, ha⟩
    have huniq :
        (∃ a : ℕ, n = 21 * a + 34 * b) ↔ ∃! a : ℕ, n = 21 * a + 34 * b := by
      constructor
      · rintro ⟨a, ha⟩
        refine ⟨a, ha, ?_⟩
        intro a' ha'
        omega
      · intro h
        exact h.exists
    have hmain : (∃! a : ℕ, n = 21 * a + 34 * b) ↔ 34 * b ≤ n := by
      simpa [b, hr] using (paper_xi_window6_tail_semigroup_two_generator_normal_form n).symm
    exact hcanon.trans (huniq.trans hmain)
  · native_decide

end Omega.Zeta
