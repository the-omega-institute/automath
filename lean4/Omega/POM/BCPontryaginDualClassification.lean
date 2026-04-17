import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Finite-coordinate model for the BC quotient side of the Pontryagin-dual classification. The
ambient dual is encoded by a tuple on `subgroupRank + bcRank`, the restriction keeps the first
`subgroupRank` coordinates, and the BC-trivial kernel keeps the last `bcRank` coordinates. -/
structure BCPontryaginDualClassificationData where
  subgroupRank : ℕ
  bcRank : ℕ
  modulus : ℕ

abbrev BCPontryaginDualClassificationData.Residue
    (D : BCPontryaginDualClassificationData) : Type :=
  Fin (D.modulus + 1)

abbrev BCPontryaginDualClassificationData.AmbientCharacter
    (D : BCPontryaginDualClassificationData) : Type :=
  Fin (D.subgroupRank + D.bcRank) → D.Residue

abbrev BCPontryaginDualClassificationData.SubgroupCharacter
    (D : BCPontryaginDualClassificationData) : Type :=
  Fin D.subgroupRank → D.Residue

abbrev BCPontryaginDualClassificationData.BCTrivialCharacter
    (D : BCPontryaginDualClassificationData) : Type :=
  Fin D.bcRank → D.Residue

/-- Restriction to the BC subgroup keeps the first `subgroupRank` coordinates. -/
def BCPontryaginDualClassificationData.restriction
    (D : BCPontryaginDualClassificationData) :
    D.AmbientCharacter → D.SubgroupCharacter :=
  fun χ i => χ (Fin.castAdd D.bcRank i)

/-- Extend a subgroup character by the trivial BC coordinates. -/
def BCPontryaginDualClassificationData.extendSubgroup
    (D : BCPontryaginDualClassificationData) :
    D.SubgroupCharacter → D.AmbientCharacter :=
  fun ψ => Fin.append ψ (fun _ => 0)

/-- Include a BC-trivial character as a character that is trivial on the subgroup coordinates. -/
def BCPontryaginDualClassificationData.bcKernelInclusion
    (D : BCPontryaginDualClassificationData) :
    D.BCTrivialCharacter → D.AmbientCharacter :=
  fun θ => Fin.append (fun _ => 0) θ

/-- Characters in the kernel are exactly those trivial on the subgroup coordinates. -/
def BCPontryaginDualClassificationData.bcKernelPred
    (D : BCPontryaginDualClassificationData) (χ : D.AmbientCharacter) : Prop :=
  ∀ i, D.restriction χ i = 0

def BCPontryaginDualClassificationData.restrictionSurjective
    (D : BCPontryaginDualClassificationData) : Prop :=
  Function.Surjective D.restriction

def BCPontryaginDualClassificationData.kernelCharacterization
    (D : BCPontryaginDualClassificationData) : Prop :=
  ∀ χ, D.bcKernelPred χ ↔ ∃ θ, D.bcKernelInclusion θ = χ

def BCPontryaginDualClassificationData.shortExactSequence
    (D : BCPontryaginDualClassificationData) : Prop :=
  Function.Injective D.bcKernelInclusion ∧
    ∀ χ, D.bcKernelPred χ ↔ χ ∈ Set.range D.bcKernelInclusion

def BCPontryaginDualClassificationData.kernelSubtype
    (D : BCPontryaginDualClassificationData) : Type :=
  { χ : D.AmbientCharacter // D.bcKernelPred χ }

def BCPontryaginDualClassificationData.kernelEquivBC
    (D : BCPontryaginDualClassificationData) :
    D.kernelSubtype ≃ D.BCTrivialCharacter where
  toFun χ := fun i => χ.1 (Fin.natAdd D.subgroupRank i)
  invFun θ :=
    ⟨D.bcKernelInclusion θ, by
      intro i
      simp [BCPontryaginDualClassificationData.restriction,
        BCPontryaginDualClassificationData.bcKernelInclusion]⟩
  left_inv χ := by
    apply Subtype.ext
    funext j
    induction j using Fin.addCases with
    | left i =>
        simpa [BCPontryaginDualClassificationData.restriction,
          BCPontryaginDualClassificationData.bcKernelInclusion] using (χ.2 i).symm
    | right i =>
        simp [BCPontryaginDualClassificationData.bcKernelInclusion]
  right_inv θ := by
    funext i
    simp [BCPontryaginDualClassificationData.bcKernelInclusion]

def BCPontryaginDualClassificationData.quotientIsomorphism
    (D : BCPontryaginDualClassificationData) : Prop :=
  Nonempty (D.kernelSubtype ≃ D.BCTrivialCharacter)

lemma restriction_surjective
    (D : BCPontryaginDualClassificationData) :
    D.restrictionSurjective := by
  intro ψ
  refine ⟨D.extendSubgroup ψ, ?_⟩
  funext i
  simp [BCPontryaginDualClassificationData.restriction,
    BCPontryaginDualClassificationData.extendSubgroup]

lemma kernel_characterization
    (D : BCPontryaginDualClassificationData) :
    D.kernelCharacterization := by
  intro χ
  constructor
  · intro hχ
    refine ⟨fun i => χ (Fin.natAdd D.subgroupRank i), ?_⟩
    funext j
    induction j using Fin.addCases with
    | left i =>
        simpa [BCPontryaginDualClassificationData.restriction,
          BCPontryaginDualClassificationData.bcKernelInclusion] using (hχ i).symm
    | right i =>
        simp [BCPontryaginDualClassificationData.bcKernelInclusion]
  · rintro ⟨θ, rfl⟩
    intro i
    simp [BCPontryaginDualClassificationData.restriction,
      BCPontryaginDualClassificationData.bcKernelInclusion]

lemma short_exact_sequence
    (D : BCPontryaginDualClassificationData) :
    D.shortExactSequence := by
  refine ⟨?_, ?_⟩
  · intro θ₁ θ₂ hθ
    funext i
    have hEval := congrFun hθ (Fin.natAdd D.subgroupRank i)
    simpa [BCPontryaginDualClassificationData.bcKernelInclusion] using hEval
  · intro χ
    constructor
    · intro hχ
      rcases kernel_characterization D χ |>.mp hχ with ⟨θ, hθ⟩
      exact ⟨θ, hθ⟩
    · rintro ⟨θ, rfl⟩
      intro i
      simp [BCPontryaginDualClassificationData.restriction,
        BCPontryaginDualClassificationData.bcKernelInclusion]

/-- Finite-coordinate version of the BC Pontryagin-dual classification: restriction to the
subgroup is surjective, its kernel is the BC-trivial part, this gives the short exact sequence,
and the kernel is canonically equivalent to the BC quotient coordinates. -/
theorem paper_pom_bc_pontryagin_dual_classification
    (D : BCPontryaginDualClassificationData) :
    D.restrictionSurjective ∧ D.kernelCharacterization ∧ D.shortExactSequence ∧
      D.quotientIsomorphism := by
  refine ⟨restriction_surjective D, kernel_characterization D, short_exact_sequence D, ?_⟩
  exact ⟨D.kernelEquivBC⟩

end Omega.POM
