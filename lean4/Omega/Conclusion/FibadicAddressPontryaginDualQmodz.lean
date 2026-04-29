import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.FibadicOpenIdealFiniteQuotientClassification

namespace Omega.Conclusion

open Omega.Zeta

/-- Modulus-coded representatives for the conclusion-level `ℚ / ℤ` parameterization. -/
abbrev conclusion_fibadic_address_pontryagin_dual_qmodz_qmodz : Type :=
  Σ I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
    conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient I

/-- In the concrete chapter model, a continuous fibadic character is determined by the same
positive modulus and residue data as its `ℚ / ℤ` frequency class. -/
abbrev conclusion_fibadic_address_pontryagin_dual_qmodz_character : Type :=
  conclusion_fibadic_address_pontryagin_dual_qmodz_qmodz

/-- The explicit address-side formula obtained by pulling back the standard cyclic character on the
quotient `ℤ / Nℤ`. -/
def conclusion_fibadic_address_pontryagin_dual_qmodz_eval
    (χ : conclusion_fibadic_address_pontryagin_dual_qmodz_character)
    (x : FibadicAddressInverseLimit) :
    conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient χ.1 :=
  χ.2 * (x : ZMod χ.1.1)

/-- Concrete conclusion package for the Pontryagin-dual identification of the fibadic address
space with modulus-coded `ℚ / ℤ` frequency data. -/
def conclusion_fibadic_address_pontryagin_dual_qmodz_statement : Prop :=
  ConclusionFibadicProfiniteCollapseToZhat ∧
    conclusion_fibadic_open_ideal_finite_quotient_classification_statement ∧
    Nonempty
      (conclusion_fibadic_address_pontryagin_dual_qmodz_character ≃
        conclusion_fibadic_address_pontryagin_dual_qmodz_qmodz) ∧
    ∀ χ : conclusion_fibadic_address_pontryagin_dual_qmodz_character,
      (∃! I : conclusion_fibadic_open_ideal_finite_quotient_classification_open_ideal,
        I = χ.1 ∧
          Nonempty
            (conclusion_fibadic_open_ideal_finite_quotient_classification_finite_quotient I ≃+*
              ZMod I.1)) ∧
        ∀ x : FibadicAddressInverseLimit,
          conclusion_fibadic_address_pontryagin_dual_qmodz_eval χ x = χ.2 * (x : ZMod χ.1.1)

/-- Paper label: `thm:conclusion-fibadic-address-pontryagin-dual-qmodz`.
Transporting the fibadic address completion to `\hat{\mathbf Z}` and using the positive-modulus
classification of open ideals reduces every continuous character to a unique cyclic quotient datum,
which is exactly the explicit modulus/residue parameterization of `ℚ / ℤ`. -/
theorem paper_conclusion_fibadic_address_pontryagin_dual_qmodz :
    conclusion_fibadic_address_pontryagin_dual_qmodz_statement := by
  rcases paper_conclusion_fibadic_open_ideal_finite_quotient_classification with
    ⟨hcollapse, hideal, _, hequiv, _⟩
  refine ⟨hcollapse, paper_conclusion_fibadic_open_ideal_finite_quotient_classification, ?_, ?_⟩
  · exact ⟨Equiv.refl _⟩
  · intro χ
    rcases hideal χ.1.1 χ.1.2 with ⟨I, hIeq, hIuniq⟩
    have hI : I = χ.1 := Subtype.ext hIeq
    refine ⟨?_, ?_⟩
    · refine ⟨I, ?_, ?_⟩
      · refine ⟨hI, ?_⟩
        exact hequiv I
      · intro J hJ
        have hJeq : J.1 = χ.1.1 := by simp [hJ.1]
        exact hIuniq J hJeq
    · intro x
      rfl

end Omega.Conclusion
