import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-abel-crossscale-chebyshev-closure-acceleration`. -/
theorem paper_xi_abel_crossscale_chebyshev_closure_acceleration
    (lam mu A B : ℤ) (S P : ℕ → ℤ)
    (hA : A = lam + mu) (hB : B = lam * mu)
    (hS : ∀ k : ℕ, S k = lam ^ k + mu ^ k)
    (hP : ∀ k : ℕ, P k = B ^ k) :
    S 0 = 2 ∧ S 1 = A ∧
      (∀ k : ℕ, 1 ≤ k → S (k + 1) = A * S k - B * S (k - 1)) ∧
        P 0 = 1 ∧ (∀ k : ℕ, P (k + 1) = B * P k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [hS]
  · simp [hS, hA]
  · intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp only [hS, hA, hB, Nat.succ_eq_add_one, Nat.add_sub_cancel_right]
    ring_nf
  · simp [hP]
  · intro k
    rw [hP (k + 1), hP k, pow_succ]
    ring

end Omega.Zeta
