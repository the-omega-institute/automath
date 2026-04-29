import Mathlib.Tactic
import Omega.Folding.BlockReservoirEncoding

namespace Omega.Folding

/-- Concrete finite data for the Block--FoldSAT NP-completeness package. The SAT witness is first
recorded as a bitstring and then pushed through the block-reservoir encoder. The remaining fields
store the verifier, the reduction, and their polynomial bounds. -/
structure BlockFoldsatNpCompleteData where
  Instance : Type
  Certificate : Type
  SatInstance : Type
  SatAssignment : SatInstance → Type
  instanceSize : Instance → ℕ
  certificateSize : Certificate → ℕ
  satSize : SatInstance → ℕ
  language : Set Instance
  verifier : Instance → Certificate → Bool
  verifierTime : Instance → Certificate → ℕ
  assignmentBits : ∀ φ, SatAssignment φ → List Bool
  witnessTail : ∀ φ, SatAssignment φ → List Bool
  witness : ∀ φ, SatAssignment φ → Certificate
  encode : SatInstance → Instance
  reductionTime : SatInstance → ℕ
  satEval : ∀ φ, SatAssignment φ → Bool
  witnessTail_eq :
    ∀ φ (a : SatAssignment φ), witnessTail φ a = blockReservoirEncode (assignmentBits φ a)
  verifier_complete :
    ∀ {x}, x ∈ language → ∃ cert, verifier x cert = true
  verifier_sound :
    ∀ {x cert}, verifier x cert = true → x ∈ language
  verifier_poly :
    ∃ k, ∀ x cert, verifierTime x cert ≤ (instanceSize x + certificateSize cert + 1) ^ k
  witness_accepts :
    ∀ φ (a : SatAssignment φ), satEval φ a = true → verifier (encode φ) (witness φ a) = true
  sat_sound :
    ∀ {φ}, encode φ ∈ language → ∃ a, satEval φ a = true
  reduction_poly :
    ∃ k, ∀ φ, reductionTime φ ≤ (satSize φ + 1) ^ k

namespace BlockFoldsatNpCompleteData

/-- The blockwise reservoir encoding used to store a SAT assignment in the FoldSAT witness tail. -/
def blockEncodedAssignment (D : BlockFoldsatNpCompleteData) (φ : D.SatInstance)
    (a : D.SatAssignment φ) : List Bool :=
  blockReservoirEncode (D.assignmentBits φ a)

/-- SAT instances that admit a concrete satisfying assignment. -/
def satLanguage (D : BlockFoldsatNpCompleteData) : Set D.SatInstance :=
  {φ | ∃ a : D.SatAssignment φ, D.satEval φ a = true}

/-- The Block--FoldSAT verifier witnesses membership in NP with a polynomial-time bound. -/
def inNP (D : BlockFoldsatNpCompleteData) : Prop :=
  ∃ k, ∀ x, x ∈ D.language ↔ ∃ cert : D.Certificate,
    D.verifier x cert = true ∧
      D.verifierTime x cert ≤ (D.instanceSize x + D.certificateSize cert + 1) ^ k

/-- The stored reduction maps SAT instances to the Block--FoldSAT language in polynomial time. -/
def satKarpReduction (D : BlockFoldsatNpCompleteData) : Prop :=
  ∃ k, ∀ φ, (φ ∈ D.satLanguage ↔ D.encode φ ∈ D.language) ∧
    D.reductionTime φ ≤ (D.satSize φ + 1) ^ k

/-- NP-completeness is the conjunction of NP-membership and SAT-hardness. -/
def npComplete (D : BlockFoldsatNpCompleteData) : Prop :=
  D.inNP ∧ D.satKarpReduction

lemma witnessTail_decodes (D : BlockFoldsatNpCompleteData) (φ : D.SatInstance)
    (a : D.SatAssignment φ) :
    blockReservoirDecode (D.witnessTail φ a) = D.assignmentBits φ a := by
  rw [D.witnessTail_eq]
  simp

lemma inNP_of_data (D : BlockFoldsatNpCompleteData) : D.inNP := by
  rcases D.verifier_poly with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro x
  constructor
  · intro hx
    rcases D.verifier_complete hx with ⟨cert, hcert⟩
    exact ⟨cert, hcert, hk x cert⟩
  · rintro ⟨cert, hcert, _⟩
    exact D.verifier_sound hcert

lemma satKarpReduction_of_data (D : BlockFoldsatNpCompleteData) : D.satKarpReduction := by
  rcases D.reduction_poly with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro φ
  refine ⟨?_, hk φ⟩
  constructor
  · rintro ⟨a, ha⟩
    have hVerifier : D.verifier (D.encode φ) (D.witness φ a) = true :=
      D.witness_accepts φ a ha
    exact D.verifier_sound hVerifier
  · intro hEncode
    exact D.sat_sound hEncode

end BlockFoldsatNpCompleteData

open BlockFoldsatNpCompleteData

/-- The block-reservoir witness encoding, the polynomial-time verifier, and the SAT reduction
combine to give NP-membership, SAT-hardness, and therefore NP-completeness.
    thm:block-foldsat-np-complete -/
theorem paper_block_foldsat_np_complete (D : BlockFoldsatNpCompleteData) :
    D.inNP ∧ D.satKarpReduction ∧ D.npComplete := by
  have hNP : D.inNP := D.inNP_of_data
  have hHard : D.satKarpReduction := D.satKarpReduction_of_data
  exact ⟨hNP, hHard, ⟨hNP, hHard⟩⟩

end Omega.Folding
