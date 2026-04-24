import Mathlib.Data.Nat.Totient

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the cyclotomic resultant degree law.
    thm:sync-cyclotomic-degree-law -/
theorem paper_etds_sync_cyclotomic_degree_law
    (degreeW : ℕ → ℕ)
    (EvenPolynomial : ℕ → Prop)
    (hDegree : ∀ m : ℕ, 4 ≤ m → degreeW m = 3 * Nat.totient (2 * m))
    (hEven : ∀ m : ℕ, 4 ≤ m → Even m → EvenPolynomial m) :
    ∀ m : ℕ, 4 ≤ m →
      degreeW m = 3 * Nat.totient (2 * m) ∧
      (Even m → EvenPolynomial m) := by
  intro m hm
  exact ⟨hDegree m hm, hEven m hm⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper preserving the explicit totient degree law used by the cyclotomic
    elimination theorem.
    thm:sync-cyclotomic-elimination-degree-law -/
theorem paper_sync_cyclotomic_elimination_degree_law
    (degreeW : ℕ → ℕ)
    (EvenPolynomial : ℕ → Prop)
    (hDegree : ∀ m : ℕ, 4 ≤ m → degreeW m = 3 * Nat.totient (2 * m))
    (hEven : ∀ m : ℕ, 4 ≤ m → Even m → EvenPolynomial m) :
    ∀ m : ℕ, 4 ≤ m →
      degreeW m = 3 * Nat.totient (2 * m) ∧
      (Even m → EvenPolynomial m) := by
  simpa using paper_etds_sync_cyclotomic_degree_law degreeW EvenPolynomial hDegree hEven

end Omega.Zeta
