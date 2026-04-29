import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-audited-even-minsector-homotopy-mod6-phase`. -/
theorem paper_xi_audited_even_minsector_homotopy_mod6_phase {X : Type} (m : Nat)
    (hm : m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12) (d : X → Nat)
    (contractible sphereLike : X → Prop) (hd : ∀ x, d x = Nat.fib (m / 2))
    (hcontractible : ∀ x, contractible x ↔ Even (d x))
    (hsphere : ∀ x, sphereLike x ↔ Odd (d x)) :
    ((m % 6 = 0 → ∀ x, contractible x) ∧
      ((m % 6 = 2 ∨ m % 6 = 4) → ∀ x, sphereLike x)) := by
  rcases hm with rfl | rfl | rfl | rfl
  · refine ⟨?_, ?_⟩
    · intro _ x
      exact (hcontractible x).2 (by rw [hd x]; norm_num [Nat.fib])
    · intro hmod
      rcases hmod with hmod | hmod <;> norm_num at hmod
  · refine ⟨?_, ?_⟩
    · intro hmod
      norm_num at hmod
    · intro _ x
      exact (hsphere x).2 (by rw [hd x]; norm_num [Nat.fib])
  · refine ⟨?_, ?_⟩
    · intro hmod
      norm_num at hmod
    · intro _ x
      exact (hsphere x).2 (by rw [hd x]; norm_num [Nat.fib])
  · refine ⟨?_, ?_⟩
    · intro _ x
      exact (hcontractible x).2 (by rw [hd x]; norm_num [Nat.fib])
    · intro hmod
      rcases hmod with hmod | hmod <;> norm_num at hmod

end Omega.Zeta
