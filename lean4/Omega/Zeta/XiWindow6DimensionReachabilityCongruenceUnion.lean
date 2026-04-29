import Mathlib.Tactic
import Omega.Zeta.XiWindow6TailSemigroupAperyThresholds

namespace Omega.Zeta

/-- Paper label: `prop:xi-window6-dimension-reachability-congruence-union`. Reachability in the
two-generator tail semigroup `⟨21,34⟩` is equivalent to belonging to one of the `21` residue
classes together with the corresponding Apéry threshold inequality. -/
theorem paper_xi_window6_dimension_reachability_congruence_union (n : ℕ) :
    let w : Fin 21 → ℕ := fun r => 34 * ((13 * r.1) % 21)
    ((∃ a c : ℕ, n = 21 * a + 34 * c) ↔ ∃ r : Fin 21, n % 21 = r.1 ∧ w r ≤ n) := by
  dsimp
  let r : Fin 21 := ⟨n % 21, Nat.mod_lt n (by decide)⟩
  have hthreshold :
      ((∃ a c : ℕ, n = 21 * a + 34 * c) ↔ 34 * ((13 * r.1) % 21) ≤ n) := by
    simpa using (paper_xi_window6_tail_semigroup_apery_thresholds.1 r n rfl)
  constructor
  · intro hn
    exact ⟨r, rfl, hthreshold.mp hn⟩
  · rintro ⟨r', hr', hw⟩
    exact (paper_xi_window6_tail_semigroup_apery_thresholds.1 r' n hr').mpr hw

end Omega.Zeta
