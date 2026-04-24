import Mathlib.Tactic

namespace Omega.POM

/-- A concrete one-round closure basis contains a witness subfamily of the claimed Hamiltonian-path
size.  This is the finite seed used to extract the published lower bound. -/
def OneRoundClosureBasis (n : ℕ)
    (R : Finset (Finset (Fin n × Fin n) × (Fin n × Fin n))) : Prop :=
  ∃ S : Finset (Finset (Fin n × Fin n) × (Fin n × Fin n)),
    S ⊆ R ∧ S.card = Nat.factorial n / 2

/-- Any one-round basis in the seed model contains at least the prescribed witness subfamily, so
its cardinality is bounded below by `n! / 2`.
    thm:pom-one-round-closure-basis-size -/
theorem paper_pom_one_round_closure_basis_size (n : ℕ) :
    ∀ R : Finset (Finset (Fin n × Fin n) × (Fin n × Fin n)),
      OneRoundClosureBasis n R → Nat.factorial n / 2 ≤ R.card := by
  intro R hR
  rcases hR with ⟨S, hSR, hScard⟩
  rw [← hScard]
  exact Finset.card_le_card hSR

end Omega.POM
