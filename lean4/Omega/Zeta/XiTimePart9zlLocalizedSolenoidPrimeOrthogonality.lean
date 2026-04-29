import Mathlib.Tactic

namespace Omega.Zeta

/-- The diagonal prime support surviving between two finite localized solenoid kernels. -/
def xi_time_part9zl_localized_solenoid_prime_orthogonality_diagonalSupport
    (S T : Finset ℕ) : Finset ℕ :=
  (S ∩ T).filter Nat.Prime

/-- An off-diagonal pair of localized prime coordinates. -/
def xi_time_part9zl_localized_solenoid_prime_orthogonality_offDiagonalPair
    (S T : Finset ℕ) (p q : ℕ) : Prop :=
  p ∈ S ∧ q ∈ T ∧ Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q

/-- Paper-facing package for finite localized solenoid prime orthogonality: the only surviving
blocks are the prime coordinates in the diagonal support, and disjoint supports leave no block. -/
def xi_time_part9zl_localized_solenoid_prime_orthogonality_statement
    (S T : Finset ℕ) : Prop :=
  (∀ p,
      p ∈ xi_time_part9zl_localized_solenoid_prime_orthogonality_diagonalSupport S T ↔
        p ∈ S ∧ p ∈ T ∧ Nat.Prime p) ∧
    (Disjoint S T →
      xi_time_part9zl_localized_solenoid_prime_orthogonality_diagonalSupport S T = ∅) ∧
    (∀ p q,
      xi_time_part9zl_localized_solenoid_prime_orthogonality_offDiagonalPair S T p q →
        p ≠ q)

/-- Paper label:
`thm:xi-time-part9zl-localized-solenoid-prime-orthogonality`. -/
theorem paper_xi_time_part9zl_localized_solenoid_prime_orthogonality (S T : Finset ℕ) :
    xi_time_part9zl_localized_solenoid_prime_orthogonality_statement S T := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    simp [xi_time_part9zl_localized_solenoid_prime_orthogonality_diagonalSupport,
      and_assoc]
  · intro hdisj
    ext p
    constructor
    · intro hp
      rw [xi_time_part9zl_localized_solenoid_prime_orthogonality_diagonalSupport,
        Finset.mem_filter, Finset.mem_inter] at hp
      exact (Finset.disjoint_left.mp hdisj hp.1.1 hp.1.2).elim
    · intro hp
      simp at hp
  · intro p q hpq
    exact hpq.2.2.2.2

end Omega.Zeta
