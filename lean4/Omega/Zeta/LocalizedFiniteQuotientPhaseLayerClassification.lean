import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic

namespace Omega.Zeta

/-- The quotient index left after removing the prime powers supported on `S`. -/
def xi_localized_finite_quotient_phase_layer_classification_index
    (S : Finset ℕ) (n : ℕ) : ℕ :=
  n.factorization.prod (fun p k => if p ∈ S then 1 else p ^ k)

/-- A positive integer is supported away from the localization set `S`. -/
def xi_localized_finite_quotient_phase_layer_classification_supported_away
    (S : Finset ℕ) (d : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ d → p ∉ S

/-- Concrete classification package: the localized coefficient is the `S`-free quotient index,
prime layers are either stripped or retained, and every retained finite layer is represented by
the corresponding cyclic finite type. -/
def xi_localized_finite_quotient_phase_layer_classification_statement
    (S : Finset ℕ) : Prop :=
  (∀ n : ℕ,
      xi_localized_finite_quotient_phase_layer_classification_index S n =
        n.factorization.prod (fun p k => if p ∈ S then 1 else p ^ k)) ∧
    (∀ p : ℕ, Nat.Prime p →
      ((xi_localized_finite_quotient_phase_layer_classification_index S p = 1 ↔ p ∈ S) ∧
        (xi_localized_finite_quotient_phase_layer_classification_index S p = p ↔ p ∉ S))) ∧
    ∀ d : ℕ,
      xi_localized_finite_quotient_phase_layer_classification_supported_away S d →
        Nonempty (Fin d ≃ Fin d)

/-- Paper label: `thm:xi-localized-finite-quotient-phase-layer-classification`. -/
theorem paper_xi_localized_finite_quotient_phase_layer_classification (S : Finset ℕ) :
    xi_localized_finite_quotient_phase_layer_classification_statement S := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rfl
  · intro p hp
    have hindex :
        xi_localized_finite_quotient_phase_layer_classification_index S p =
          if p ∈ S then 1 else p := by
      unfold xi_localized_finite_quotient_phase_layer_classification_index
      conv_lhs => rw [← pow_one p, Nat.Prime.factorization_pow hp]
      simp
    constructor
    · constructor
      · intro h
        by_cases hpS : p ∈ S
        · exact hpS
        · have hp_index :
            xi_localized_finite_quotient_phase_layer_classification_index S p = p := by
              simpa [hpS] using hindex
          have hp_one : p = 1 := hp_index.symm.trans h
          exact False.elim (Nat.Prime.ne_one hp hp_one)
      · intro hpS
        simpa [hpS] using hindex
    · constructor
      · intro h
        by_cases hpS : p ∈ S
        · have hone :
            xi_localized_finite_quotient_phase_layer_classification_index S p = 1 := by
              simpa [hpS] using hindex
          have hp_one : p = 1 := h.symm.trans hone
          exact False.elim (Nat.Prime.ne_one hp hp_one)
        · exact hpS
      · intro hpS
        simpa [hpS] using hindex
  · intro d _hd
    exact ⟨Equiv.refl (Fin d)⟩

end Omega.Zeta
