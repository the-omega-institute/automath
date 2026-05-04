import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-atomic-witt-unweighted-unique-two-step-class`. -/
theorem paper_xi_atomic_witt_unweighted_unique_two_step_class (p pCore a aCore : ℕ → ℕ)
    (hP : ∀ n, p n = pCore n + if n = 2 then 1 else 0)
    (hA : ∀ n, a n = aCore n + if 2 ∣ n then 2 else 0) :
    (∀ n, p n = pCore n + if n = 2 then 1 else 0) ∧
      (∀ n, a n = aCore n + if 2 ∣ n then 2 else 0) ∧
      (∀ m, 1 ≤ m → a (2 * m) - aCore (2 * m) = 2) ∧
      (∀ m, a (2 * m + 1) - aCore (2 * m + 1) = 0) := by
  refine ⟨hP, hA, ?_, ?_⟩
  · intro m _hm
    rw [hA]
    simp
  · intro m
    have hodd : ¬2 ∣ 2 * m + 1 := by
      rintro ⟨c, hc⟩
      omega
    rw [hA]
    simp [hodd]

end Omega.Zeta
