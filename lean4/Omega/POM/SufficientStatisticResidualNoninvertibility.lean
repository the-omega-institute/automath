import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.POM.SufficientStatisticResidualNoninvertibility

/-- A residual taking values in `Fin (d_x + 1)` cannot be injective on a larger finite type.
    prop:pom-sufficient-statistic-residual-noninvertibility -/
theorem paper_pom_sufficient_statistic_residual_noninvertibility {Ω : Type*} [Fintype Ω]
    (d_x : ℕ) (ℛ : Ω → Fin (d_x + 1)) (hbig : d_x + 1 < Fintype.card Ω) :
    ¬ Function.Injective ℛ := by
  intro hℛ
  have hcard : Fintype.card Ω ≤ d_x + 1 := by
    simpa using Fintype.card_le_of_injective ℛ hℛ
  exact (Nat.not_lt_of_ge hcard) hbig

/-- Any prime divisor of a Fibonacci-factorized fiber multiplicity already divides one
shifted Fibonacci factor from the decomposition, and the factor index is bounded by the
maximal path length.
    cor:pom-fiber-multiplicity-fibonacci-prime-closure -/
theorem paper_pom_fiber_multiplicity_fibonacci_prime_closure (m : ℕ) (L : List ℕ) (dm : ℕ)
    (hprod : dm = (L.map fun ℓ => Nat.fib (ℓ + 2)).prod) (hlen : ∀ ℓ ∈ L, ℓ ≤ m) :
    ∀ p : ℕ, Nat.Prime p → p ∣ dm → ∃ r ≤ m + 2, p ∣ Nat.fib r := by
  have hmain :
      ∀ K : List ℕ, (∀ ℓ ∈ K, ℓ ≤ m) →
        ∀ p : ℕ, Nat.Prime p → p ∣ (K.map fun ℓ => Nat.fib (ℓ + 2)).prod →
          ∃ r ≤ m + 2, p ∣ Nat.fib r := by
    intro K
    induction K with
    | nil =>
        intro hK p hp hdiv
        simp at hdiv
        exact (hp.ne_one hdiv).elim
    | cons ℓ K ih =>
        intro hK p hp hdiv
        simp only [List.map_cons, List.prod_cons] at hdiv
        rcases hp.dvd_mul.mp hdiv with hhead | htail
        · refine ⟨ℓ + 2, ?_, hhead⟩
          have hℓ : ℓ ≤ m := hK ℓ (by simp)
          omega
        · refine ih (by
            intro ℓ' hmem
            exact hK ℓ' (by simp [hmem])) p hp htail
  intro p hp hdm
  rw [hprod] at hdm
  exact hmain L hlen p hp hdm

end Omega.POM.SufficientStatisticResidualNoninvertibility
