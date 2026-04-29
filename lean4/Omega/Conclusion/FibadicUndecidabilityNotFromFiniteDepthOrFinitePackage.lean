import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.Conclusion.FibadicOpenIdealFiniteQuotientClassification

namespace Omega.Conclusion

/-- The finite-valued fibadic observable carried by this finite package: a positive conductor and
a value in its cyclic finite quotient. -/
abbrev conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_observable :
    Type :=
  Σ I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
    conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient I

/-- Concrete finite conductor / prime-package data. The finite predicate records that every visible
prime package divides the selected conductor bound. -/
structure conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_data where
  conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_conductorBound : ℕ
  conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_primePackage :
    Finset ℕ
  conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_observable :
    conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_observable

namespace conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_data

/-- The finite arithmetic predicate checked by enumeration of the recorded prime package. -/
def finite_package_predicate
    (D : conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_data) :
    Prop :=
  ∀ p ∈
      D.conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_primePackage,
    p ∣
      D.conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_conductorBound

/-- Finite package predicates are decidable by finite enumeration. -/
def finite_data_decidable
    (D : conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_data) :
    Prop :=
  Nonempty (Decidable D.finite_package_predicate)

/-- No undecidability can be witnessed by this finite datum: its finite predicate has a decision
verdict, and the fibadic finite-observable conductor reduction is already available. -/
def no_finite_data_undecidability
    (D : conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_data) :
    Prop :=
  conclusion_fibadic_open_ideal_finite_quotient_classification_statement ∧
    ¬ (D.finite_package_predicate ∧ ¬ D.finite_data_decidable)

end conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_data

/-- Paper label:
`cor:conclusion-fibadic-undecidability-not-from-finite-depth-or-finite-package`. -/
theorem paper_conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package
    (D : conclusion_fibadic_undecidability_not_from_finite_depth_or_finite_package_data) :
    D.finite_data_decidable ∧ D.no_finite_data_undecidability := by
  classical
  have hdec : D.finite_data_decidable := ⟨inferInstance⟩
  refine ⟨hdec, ?_⟩
  refine ⟨paper_conclusion_fibadic_open_ideal_finite_quotient_classification, ?_⟩
  intro hbad
  exact hbad.2 hdec

end Omega.Conclusion
