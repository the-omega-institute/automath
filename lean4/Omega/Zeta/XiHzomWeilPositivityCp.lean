import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete rank-one Hermitian correlation data for the quadratic HZOM positivity package. -/
structure xi_hzom_weil_positivity_cp_data where
  xi_hzom_weil_positivity_cp_tests : Type
  xi_hzom_weil_positivity_cp_observable : xi_hzom_weil_positivity_cp_tests → ℂ

namespace xi_hzom_weil_positivity_cp_data

/-- The Hermitian correlation form attached to the concrete observable. -/
noncomputable def xi_hzom_weil_positivity_cp_correlation
    (D : xi_hzom_weil_positivity_cp_data)
    (f g : D.xi_hzom_weil_positivity_cp_tests) : ℂ :=
  star (D.xi_hzom_weil_positivity_cp_observable f) *
    D.xi_hzom_weil_positivity_cp_observable g

/-- The finite quadratic energy of a linear combination of tests. -/
noncomputable def xi_hzom_weil_positivity_cp_quadratic_energy
    (D : xi_hzom_weil_positivity_cp_data) {n : ℕ}
    (f : Fin n → D.xi_hzom_weil_positivity_cp_tests) (z : Fin n → ℂ) : ℝ :=
  Complex.normSq (∑ i, z i * D.xi_hzom_weil_positivity_cp_observable (f i))

/-- Finite Gram positive semidefiniteness for the correlation form. -/
def xi_hzom_weil_positivity_cp_finite_gram_psd
    (D : xi_hzom_weil_positivity_cp_data) : Prop :=
  ∀ (n : ℕ) (f : Fin n → D.xi_hzom_weil_positivity_cp_tests) (z : Fin n → ℂ),
    0 ≤ D.xi_hzom_weil_positivity_cp_quadratic_energy f z

/-- Nonnegativity of all finite quadratic tests. -/
def xi_hzom_weil_positivity_cp_quadratic_nonnegative
    (D : xi_hzom_weil_positivity_cp_data) : Prop :=
  ∀ (n : ℕ) (f : Fin n → D.xi_hzom_weil_positivity_cp_tests) (z : Fin n → ℂ),
    0 ≤ D.xi_hzom_weil_positivity_cp_quadratic_energy f z

/-- Existence of a rank-one Gram representation of the Hermitian correlation form. -/
def xi_hzom_weil_positivity_cp_gram_representation
    (D : xi_hzom_weil_positivity_cp_data) : Prop :=
  ∃ X : D.xi_hzom_weil_positivity_cp_tests → ℂ,
    ∀ f g,
      D.xi_hzom_weil_positivity_cp_correlation f g = star (X f) * X g

/-- The three concrete positivity certificates are available and the first two coincide. -/
def xi_hzom_weil_positivity_cp_statement
    (D : xi_hzom_weil_positivity_cp_data) : Prop :=
  D.xi_hzom_weil_positivity_cp_finite_gram_psd ∧
    D.xi_hzom_weil_positivity_cp_quadratic_nonnegative ∧
      D.xi_hzom_weil_positivity_cp_gram_representation ∧
        (D.xi_hzom_weil_positivity_cp_finite_gram_psd ↔
          D.xi_hzom_weil_positivity_cp_quadratic_nonnegative)

end xi_hzom_weil_positivity_cp_data

/-- Paper label: `prop:xi-hzom-weil-positivity-cp`. -/
theorem paper_xi_hzom_weil_positivity_cp
    (D : xi_hzom_weil_positivity_cp_data) :
    D.xi_hzom_weil_positivity_cp_statement := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n f z
    exact Complex.normSq_nonneg _
  · intro n f z
    exact Complex.normSq_nonneg _
  · refine ⟨D.xi_hzom_weil_positivity_cp_observable, ?_⟩
    intro f g
    rfl
  · constructor <;> intro h <;> exact h

end Omega.Zeta
