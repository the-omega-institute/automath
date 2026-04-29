import Mathlib.Tactic
import Omega.Conclusion.FibadicOpenIdealFiniteQuotientClassification

namespace Omega.Conclusion

/-- Concrete finite-valued observables on the fibadic side are encoded by a modulus-coded open
ideal together with a value in the corresponding cyclic finite quotient. -/
abbrev conclusion_fibadic_finite_valued_observable_conductor_observable : Type :=
  Σ I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
    conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient I

/-- The minimal conductor carried by the observable is the modulus of its classified finite
quotient. -/
abbrev conclusion_fibadic_finite_valued_observable_conductor_conductor
    (χ : conclusion_fibadic_finite_valued_observable_conductor_observable) :
    conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal :=
  χ.1

/-- Factoring through a finite fibadic quotient is recorded by divisibility of the corresponding
modulus-coded open ideal. -/
def conclusion_fibadic_finite_valued_observable_conductor_factors_through
    (χ : conclusion_fibadic_finite_valued_observable_conductor_observable)
    (I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal) : Prop :=
  (conclusion_fibadic_finite_valued_observable_conductor_conductor χ).1 ∣ I.1

/-- Paper-facing conductor package for finite-valued fibadic observables: after transporting to
modulus-coded finite quotients of `\hat{\mathbf Z}`, every observable has a unique minimal
conductor, and factorization through any other finite quotient is exactly divisibility by that
conductor. -/
def conclusion_fibadic_finite_valued_observable_conductor_statement : Prop :=
  conclusion_fibadic_open_ideal_finite_quotient_classification_statement ∧
    ∀ χ : conclusion_fibadic_finite_valued_observable_conductor_observable,
      (∃!
          I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
            conclusion_fibadic_finite_valued_observable_conductor_factors_through χ I ∧
              ∀ J : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
                conclusion_fibadic_finite_valued_observable_conductor_factors_through χ J →
                  I.1 ∣ J.1) ∧
        ∀ J : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
          conclusion_fibadic_finite_valued_observable_conductor_factors_through χ J ↔
            (conclusion_fibadic_finite_valued_observable_conductor_conductor χ).1 ∣ J.1

/-- Paper label: `thm:conclusion-fibadic-finite-valued-observable-conductor`. -/
theorem paper_conclusion_fibadic_finite_valued_observable_conductor :
    conclusion_fibadic_finite_valued_observable_conductor_statement := by
  refine ⟨paper_conclusion_fibadic_open_ideal_finite_quotient_classification, ?_⟩
  intro χ
  let I := conclusion_fibadic_finite_valued_observable_conductor_conductor χ
  refine ⟨?_, ?_⟩
  · refine ⟨I, ?_, ?_⟩
    · refine ⟨dvd_rfl, ?_⟩
      intro J hJ
      exact hJ
    · intro J hJ
      have hJI : J.1 ∣ I.1 := hJ.2 I dvd_rfl
      have hIJ : I.1 ∣ J.1 := hJ.1
      exact Subtype.ext (dvd_antisymm hJI hIJ)
  · intro J
    rfl

end Omega.Conclusion
