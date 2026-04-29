import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part28c-artin-strip-offline-count-additivity`. -/
theorem paper_xi_time_part28c_artin_strip_offline_count_additivity {ι : Type*}
    [Fintype ι] (d ν : ι → ℕ) (N : ℕ → ℕ) (Nρ : ι → ℕ → ℕ)
    (hN : ∀ T, N T = ∑ ρ, d ρ * Nρ ρ T) (hd : ∀ ρ, 0 < d ρ) :
    (∀ T, N T = ∑ ρ, d ρ * Nρ ρ T) ∧
      ((∑ ρ, d ρ * ν ρ) = 0 ↔ ∀ ρ, ν ρ = 0) := by
  constructor
  · exact hN
  · constructor
    · intro hsum ρ
      by_contra hν
      have hνpos : 0 < ν ρ := Nat.pos_of_ne_zero hν
      have hterm_pos : 0 < d ρ * ν ρ := Nat.mul_pos (hd ρ) hνpos
      have hterm_le : d ρ * ν ρ ≤ ∑ σ, d σ * ν σ :=
        Finset.single_le_sum (f := fun σ => d σ * ν σ)
          (by intro σ hσ; exact Nat.zero_le _) (Finset.mem_univ ρ)
      rw [hsum] at hterm_le
      exact (Nat.not_lt_zero _ (lt_of_lt_of_le hterm_pos hterm_le)).elim
    · intro hzero
      simp [hzero]

end Omega.Zeta
