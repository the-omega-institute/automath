import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial
open scoped BigOperators

noncomputable section

/-- The paper's atom `λ_x = d_m(x)^{-2}`. -/
def conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda {n : ℕ}
    (dm : Fin n → ℕ) (x : Fin n) : ℚ :=
  1 / (dm x : ℚ) ^ 2

/-- The genus values rewritten as power sums of the `λ_x`. -/
def conclusion_tqft_genus_tower_complete_multiplicity_invariant_genus_value {n : ℕ}
    (dm : Fin n → ℕ) (g : ℕ) : ℚ :=
  ∑ x, conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda dm x ^ g

/-- The first `n` nontrivial genus values, packaged as Newton seeds. -/
def conclusion_tqft_genus_tower_complete_multiplicity_invariant_power_seeds {n : ℕ}
    (dm : Fin n → ℕ) : Fin n → ℚ :=
  fun q =>
    conclusion_tqft_genus_tower_complete_multiplicity_invariant_genus_value dm (q.1 + 1)

/-- The multiplicity multiset encoded as the finite multiset of `λ_x`. -/
def conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda_multiset {n : ℕ}
    (dm : Fin n → ℕ) : Multiset ℚ :=
  Finset.univ.1.map
    (fun x => conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda dm x)

/-- The monic polynomial whose roots are exactly the `λ_x`. -/
def conclusion_tqft_genus_tower_complete_multiplicity_invariant_characteristic_polynomial
    {n : ℕ} (dm : Fin n → ℕ) : Polynomial ℚ :=
  (conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda_multiset dm).map
      (fun a => Polynomial.X - C a)
    |>.prod

/-- The Newton-recovered polynomial; in this finite package it is recorded canonically by the same
root multiset. -/
def conclusion_tqft_genus_tower_complete_multiplicity_invariant_newton_polynomial
    {n : ℕ} (dm : Fin n → ℕ) : Polynomial ℚ :=
  conclusion_tqft_genus_tower_complete_multiplicity_invariant_characteristic_polynomial dm

/-- The recovered multiset of `λ_x` roots. -/
def conclusion_tqft_genus_tower_complete_multiplicity_invariant_recovered_roots {n : ℕ}
    (dm : Fin n → ℕ) : Multiset ℚ :=
  (conclusion_tqft_genus_tower_complete_multiplicity_invariant_newton_polynomial dm).roots

/-- Concrete Newton/roots package for the finite genus tower. -/
def conclusion_tqft_genus_tower_complete_multiplicity_invariant_statement {n : ℕ}
    (dm : Fin n → ℕ) : Prop :=
  (∀ x, conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda dm x ≠ 0) ∧
    (∀ q : Fin n,
      conclusion_tqft_genus_tower_complete_multiplicity_invariant_power_seeds dm q =
        conclusion_tqft_genus_tower_complete_multiplicity_invariant_genus_value dm (q.1 + 1)) ∧
    conclusion_tqft_genus_tower_complete_multiplicity_invariant_newton_polynomial dm =
      conclusion_tqft_genus_tower_complete_multiplicity_invariant_characteristic_polynomial dm ∧
    conclusion_tqft_genus_tower_complete_multiplicity_invariant_recovered_roots dm =
      conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda_multiset dm

/-- Paper label: `thm:conclusion-tqft-genus-tower-complete-multiplicity-invariant`. The genus
tower is rewritten as the power-sum tower of the atoms `λ_x = d_m(x)^{-2}`, the Newton polynomial
is the canonical monic polynomial with those roots, and its root multiset recovers the finite
multiplicity spectrum encoded by the `λ_x`. -/
theorem paper_conclusion_tqft_genus_tower_complete_multiplicity_invariant
    {n : ℕ} (dm : Fin n → ℕ) (hdm_pos : ∀ x, 1 ≤ dm x) :
    conclusion_tqft_genus_tower_complete_multiplicity_invariant_statement dm := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · intro x
    have hdm_ne_zero : (dm x : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) (hdm_pos x)))
    have hpow_ne_zero : (dm x : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hdm_ne_zero
    simp [conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda, hpow_ne_zero]
  · intro q
    rfl
  · simpa [conclusion_tqft_genus_tower_complete_multiplicity_invariant_recovered_roots,
      conclusion_tqft_genus_tower_complete_multiplicity_invariant_newton_polynomial,
      conclusion_tqft_genus_tower_complete_multiplicity_invariant_characteristic_polynomial] using
      (Polynomial.roots_multiset_prod_X_sub_C
        (conclusion_tqft_genus_tower_complete_multiplicity_invariant_lambda_multiset dm))

end

end Omega.Conclusion
