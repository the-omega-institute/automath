import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic
import Omega.POM.BCPontryaginDualClassification

namespace Omega.Conclusion

/-- Finite-coordinate wrapper for the derived strictification/Pontryagin classification. The
finite BC quotient is modeled by the last `bcRank` coordinates, while the first `subgroupRank`
coordinates record the fiberwise directions annihilated by BC factorization. -/
structure DerivedStrictificationPontryaginData where
  subgroupRank : ℕ
  bcRank : ℕ
  modulus : ℕ

namespace DerivedStrictificationPontryaginData

abbrev Residue (D : DerivedStrictificationPontryaginData) : Type :=
  Fin (D.modulus + 1)

abbrev AmbientCharacter (D : DerivedStrictificationPontryaginData) : Type :=
  Fin (D.subgroupRank + D.bcRank) → D.Residue

abbrev BCCharacter (D : DerivedStrictificationPontryaginData) : Type :=
  Fin D.bcRank → D.Residue

/-- The BC quotient package used by the existing finite-coordinate Pontryagin classification. -/
def toBCPontryaginData
    (D : DerivedStrictificationPontryaginData) : Omega.POM.BCPontryaginDualClassificationData where
  subgroupRank := D.subgroupRank
  bcRank := D.bcRank
  modulus := D.modulus

/-- Extend a BC-quotient character by the trivial fiberwise coordinates. -/
def bcLift (D : DerivedStrictificationPontryaginData) :
    D.BCCharacter → D.AmbientCharacter :=
  fun θ => Fin.append (fun _ => 0) θ

/-- Fiberwise constancy means the character is trivial on the coordinates collapsed by the BC
quotient. -/
def fiberwiseConstancy (D : DerivedStrictificationPontryaginData)
    (χ : D.AmbientCharacter) : Prop :=
  ∀ i, χ (Fin.castAdd D.bcRank i) = 0

/-- Factoring through the BC quotient means coming from a character on the quotient coordinates. -/
def factorsThroughBC (D : DerivedStrictificationPontryaginData)
    (χ : D.AmbientCharacter) : Prop :=
  ∃ θ, D.bcLift θ = χ

/-- Quotient-universal-property form of the factorization criterion. -/
def fiberwiseConstancyIffFactorsThroughBC (D : DerivedStrictificationPontryaginData) : Prop :=
  ∀ χ, D.fiberwiseConstancy χ ↔ D.factorsThroughBC χ

/-- Pontryagin-dual exactness is the short exact sequence already classified on the BC side. -/
def pontryaginDualShortExact (D : DerivedStrictificationPontryaginData) : Prop :=
  D.toBCPontryaginData.shortExactSequence

lemma fiberwise_constancy_iff_factors_through_bc
    (D : DerivedStrictificationPontryaginData) (χ : D.AmbientCharacter) :
    D.fiberwiseConstancy χ ↔ D.factorsThroughBC χ := by
  constructor
  · intro hχ
    refine ⟨fun i => χ (Fin.natAdd D.subgroupRank i), ?_⟩
    funext j
    induction j using Fin.addCases with
    | left i =>
        simpa [fiberwiseConstancy, bcLift] using (hχ i).symm
    | right i =>
        simp [bcLift]
  · rintro ⟨θ, rfl⟩
    intro i
    simp [bcLift]

end DerivedStrictificationPontryaginData

/-- Paper label: `thm:derived-strictification-pontryagin-complete-classification`. -/
theorem paper_derived_strictification_pontryagin_complete_classification
    (D : DerivedStrictificationPontryaginData) :
    D.fiberwiseConstancyIffFactorsThroughBC ∧ D.pontryaginDualShortExact := by
  refine ⟨?_, ?_⟩
  · intro χ
    exact D.fiberwise_constancy_iff_factors_through_bc χ
  · exact
      (Omega.POM.paper_pom_bc_pontryagin_dual_classification D.toBCPontryaginData).2.2.1

end Omega.Conclusion
