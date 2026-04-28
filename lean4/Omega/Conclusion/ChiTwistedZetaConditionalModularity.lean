import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs

namespace Omega.Conclusion

/-- Concrete data for the conditional modularity transfer.  The finite Euler-factor comparison and
the Artin weight-one input are stated as equalities of explicit local factor functions. -/
structure conclusion_chi_twisted_zeta_conditional_modularity_data where
  conclusion_chi_twisted_zeta_conditional_modularity_bad_primes : Finset ℕ
  conclusion_chi_twisted_zeta_conditional_modularity_chi_euler_factor : ℕ → ℚ
  conclusion_chi_twisted_zeta_conditional_modularity_artin_euler_factor : ℕ → ℚ
  conclusion_chi_twisted_zeta_conditional_modularity_modular_euler_factor : ℕ → ℚ
  conclusion_chi_twisted_zeta_conditional_modularity_primitive_euler_factor : ℕ → ℚ
  conclusion_chi_twisted_zeta_conditional_modularity_modular_radius : ℚ
  conclusion_chi_twisted_zeta_conditional_modularity_inherited_radius : ℚ
  conclusion_chi_twisted_zeta_conditional_modularity_chi_matches_artin :
    ∀ p,
      Nat.Prime p →
      p ∉ conclusion_chi_twisted_zeta_conditional_modularity_bad_primes →
        conclusion_chi_twisted_zeta_conditional_modularity_chi_euler_factor p =
          conclusion_chi_twisted_zeta_conditional_modularity_artin_euler_factor p
  conclusion_chi_twisted_zeta_conditional_modularity_artin_weight_one :
    ∀ p,
      Nat.Prime p →
      p ∉ conclusion_chi_twisted_zeta_conditional_modularity_bad_primes →
        conclusion_chi_twisted_zeta_conditional_modularity_artin_euler_factor p =
          conclusion_chi_twisted_zeta_conditional_modularity_modular_euler_factor p
  conclusion_chi_twisted_zeta_conditional_modularity_primitive_matches_chi :
    ∀ p,
      Nat.Prime p →
      p ∉ conclusion_chi_twisted_zeta_conditional_modularity_bad_primes →
        conclusion_chi_twisted_zeta_conditional_modularity_primitive_euler_factor p =
          conclusion_chi_twisted_zeta_conditional_modularity_chi_euler_factor p
  conclusion_chi_twisted_zeta_conditional_modularity_analytic_transfer :
    conclusion_chi_twisted_zeta_conditional_modularity_inherited_radius =
      conclusion_chi_twisted_zeta_conditional_modularity_modular_radius
  conclusion_chi_twisted_zeta_conditional_modularity_modular_radius_nonnegative :
    0 ≤ conclusion_chi_twisted_zeta_conditional_modularity_modular_radius

/-- The primitive twisted zeta factor agrees with the weight-one modular factor away from the
finite exceptional set and inherits the same analytic radius proxy. -/
def conclusion_chi_twisted_zeta_conditional_modularity_statement
    (D : conclusion_chi_twisted_zeta_conditional_modularity_data) : Prop :=
  (∀ p,
      Nat.Prime p →
      p ∉ D.conclusion_chi_twisted_zeta_conditional_modularity_bad_primes →
        D.conclusion_chi_twisted_zeta_conditional_modularity_primitive_euler_factor p =
          D.conclusion_chi_twisted_zeta_conditional_modularity_modular_euler_factor p) ∧
    D.conclusion_chi_twisted_zeta_conditional_modularity_inherited_radius =
      D.conclusion_chi_twisted_zeta_conditional_modularity_modular_radius ∧
    0 ≤ D.conclusion_chi_twisted_zeta_conditional_modularity_inherited_radius

/-- Paper label: `cor:conclusion-chi-twisted-zeta-conditional-modularity`. -/
theorem paper_conclusion_chi_twisted_zeta_conditional_modularity
    (D : conclusion_chi_twisted_zeta_conditional_modularity_data) :
    conclusion_chi_twisted_zeta_conditional_modularity_statement D := by
  refine ⟨?_, D.conclusion_chi_twisted_zeta_conditional_modularity_analytic_transfer, ?_⟩
  · intro p hp hnot
    calc
      D.conclusion_chi_twisted_zeta_conditional_modularity_primitive_euler_factor p =
          D.conclusion_chi_twisted_zeta_conditional_modularity_chi_euler_factor p :=
        D.conclusion_chi_twisted_zeta_conditional_modularity_primitive_matches_chi p hp hnot
      _ = D.conclusion_chi_twisted_zeta_conditional_modularity_artin_euler_factor p :=
        D.conclusion_chi_twisted_zeta_conditional_modularity_chi_matches_artin p hp hnot
      _ = D.conclusion_chi_twisted_zeta_conditional_modularity_modular_euler_factor p :=
        D.conclusion_chi_twisted_zeta_conditional_modularity_artin_weight_one p hp hnot
  · rw [D.conclusion_chi_twisted_zeta_conditional_modularity_analytic_transfer]
    exact D.conclusion_chi_twisted_zeta_conditional_modularity_modular_radius_nonnegative

end Omega.Conclusion
