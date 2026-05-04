import Mathlib.Tactic

namespace Omega.Zeta

/-- A cyclic audit chain: the moduli grow by divisibility, and stage `k` audits `D (2 * k)`. -/
def xi_minimal_cyclic_audit_chain_universal_chain (D M : ℕ → ℕ) : Prop :=
  (∀ k, M k ∣ M (k + 1)) ∧ ∀ k, D (2 * k) ∣ M k

/-- The minimal chain is generated recursively by adjoining each audited modulus by lcm. -/
def xi_minimal_cyclic_audit_chain_universal_lcm_chain (D N : ℕ → ℕ) : Prop :=
  N 0 = D 0 ∧ ∀ k, N (k + 1) = Nat.lcm (N k) (D (2 * (k + 1)))

/-- Paper label: `thm:xi-minimal-cyclic-audit-chain-universal`. -/
theorem paper_xi_minimal_cyclic_audit_chain_universal (D N : ℕ → ℕ)
    (isLcmChain : xi_minimal_cyclic_audit_chain_universal_lcm_chain D N)
    (surjectiveLimitMap : (ℕ → ℕ) → (ℕ → ℕ) → Prop)
    (map_of_levelwise_dvd : ∀ M, (∀ k, N k ∣ M k) → surjectiveLimitMap M N) :
    xi_minimal_cyclic_audit_chain_universal_chain D N ∧
      ∀ M, xi_minimal_cyclic_audit_chain_universal_chain D M →
        (∀ k, N k ∣ M k) ∧ surjectiveLimitMap M N := by
  rcases isLcmChain with ⟨hN0, hNsucc⟩
  have hN_chain : xi_minimal_cyclic_audit_chain_universal_chain D N := by
    constructor
    · intro k
      rw [hNsucc k]
      exact Nat.dvd_lcm_left _ _
    · intro k
      cases k with
      | zero =>
          simp [hN0]
      | succ k =>
          rw [hNsucc k]
          exact Nat.dvd_lcm_right _ _
  refine ⟨hN_chain, ?_⟩
  intro M hM
  rcases hM with ⟨hMstep, hMD⟩
  have hminimal : ∀ k, N k ∣ M k := by
    intro k
    induction k with
    | zero =>
        simpa [hN0] using hMD 0
    | succ k ih =>
        have hN_to_next : N k ∣ M (k + 1) := dvd_trans ih (hMstep k)
        have hD_to_next : D (2 * (k + 1)) ∣ M (k + 1) := hMD (k + 1)
        rw [hNsucc k]
        exact Nat.lcm_dvd hN_to_next hD_to_next
  exact ⟨hminimal, map_of_levelwise_dvd M hminimal⟩

end Omega.Zeta
