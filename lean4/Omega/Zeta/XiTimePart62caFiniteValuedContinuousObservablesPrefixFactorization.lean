import Mathlib.Tactic

namespace Omega.Zeta

universe u v

/-- Concrete data for finite-prefix dependence of a finite-valued stream observable. -/
structure xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_data where
  Alphabet : Type u
  Value : Type v
  prefixLength : ℕ
  finiteValue : Fintype Value
  observe : (ℕ → Alphabet) → Value

/-- The length-`prefixLength` coordinate prefix of a stream. -/
def xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_prefix
    (D : xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_data)
    (x : ℕ → D.Alphabet) : Fin D.prefixLength → D.Alphabet :=
  fun i => x i

/-- Prefix-factorization statement: the observable descends to the finite prefix image. -/
def xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_statement
    (D : xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_data) :
    Prop :=
  (∀ x y : ℕ → D.Alphabet,
      (∀ i : Fin D.prefixLength, x i = y i) → D.observe x = D.observe y) →
    ∃ F :
      Set.range
          (xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_prefix D) →
        D.Value,
      ∀ x : ℕ → D.Alphabet,
        F ⟨xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_prefix D x,
            ⟨x, rfl⟩⟩ =
          D.observe x

/-- Paper label:
`cor:xi-time-part62ca-finite-valued-continuous-observables-prefix-factorization`. -/
theorem paper_xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization
    (D : xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_data) :
    xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_statement D := by
  intro huniform
  refine ⟨fun p => D.observe p.2.choose, ?_⟩
  intro x
  let p : Set.range
      (xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_prefix D) :=
    ⟨xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_prefix D x,
      ⟨x, rfl⟩⟩
  change D.observe p.2.choose = D.observe x
  apply huniform
  intro i
  have hprefix :
      xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_prefix D
          p.2.choose =
        xi_time_part62ca_finite_valued_continuous_observables_prefix_factorization_prefix D x :=
    p.2.choose_spec
  exact congrFun hprefix i

end Omega.Zeta
