import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Folding.BlockFoldsatNpComplete

namespace Omega.Folding

/-- Paper label: `thm:block-foldsat-sharpP-complete`. Unpack the existing Block--FoldSAT
NP-complete infrastructure into an explicit counting statement: the verifier relation is still in
NP, the SAT reduction is still polynomial, the reservoir tail decodes to the original assignment,
and an explicit bijection identifies accepted witness microstates with satisfying assignments. -/
theorem paper_block_foldsat_sharpp_complete
    {Instance Certificate SatInstance : Type}
    [Fintype Certificate]
    (SatAssignment : SatInstance → Type)
    [∀ φ : SatInstance, Fintype (SatAssignment φ)]
    (instanceSize : Instance → ℕ)
    (certificateSize : Certificate → ℕ)
    (satSize : SatInstance → ℕ)
    (language : Set Instance)
    (verifier : Instance → Certificate → Bool)
    (verifierTime : Instance → Certificate → ℕ)
    (assignmentBits : ∀ φ, SatAssignment φ → List Bool)
    (witnessTail : ∀ φ, SatAssignment φ → List Bool)
    (witness : ∀ φ, SatAssignment φ → Certificate)
    (encode : SatInstance → Instance)
    (reductionTime : SatInstance → ℕ)
    (satEval : ∀ φ, SatAssignment φ → Bool)
    (witnessTail_eq :
      ∀ φ (a : SatAssignment φ), witnessTail φ a = blockReservoirEncode (assignmentBits φ a))
    (verifier_complete :
      ∀ {x}, x ∈ language → ∃ cert, verifier x cert = true)
    (verifier_sound :
      ∀ {x cert}, verifier x cert = true → x ∈ language)
    (verifier_poly :
      ∃ k, ∀ x cert, verifierTime x cert ≤ (instanceSize x + certificateSize cert + 1) ^ k)
    (witness_accepts :
      ∀ φ (a : SatAssignment φ), satEval φ a = true → verifier (encode φ) (witness φ a) = true)
    (sat_sound :
      ∀ {φ}, encode φ ∈ language → ∃ a, satEval φ a = true)
    (reduction_poly :
      ∃ k, ∀ φ, reductionTime φ ≤ (satSize φ + 1) ^ k)
    (witness_bijective :
      ∀ φ,
        Function.Bijective
          (fun a : {a : SatAssignment φ // satEval φ a = true} =>
            (⟨witness φ a.1, witness_accepts φ a.1 a.2⟩ :
              {cert : Certificate // verifier (encode φ) cert = true}))) :
    (∃ k, ∀ x, x ∈ language ↔ ∃ cert : Certificate,
        verifier x cert = true ∧
          verifierTime x cert ≤ (instanceSize x + certificateSize cert + 1) ^ k) ∧
      (∃ k, ∀ φ, ((∃ a : SatAssignment φ, satEval φ a = true) ↔ encode φ ∈ language) ∧
        reductionTime φ ≤ (satSize φ + 1) ^ k) ∧
      (∀ φ (a : SatAssignment φ), blockReservoirDecode (witnessTail φ a) = assignmentBits φ a) ∧
      (∀ φ,
        Fintype.card {cert : Certificate // verifier (encode φ) cert = true} =
          Fintype.card {a : SatAssignment φ // satEval φ a = true}) := by
  let D : BlockFoldsatNpCompleteData :=
    { Instance := Instance
      Certificate := Certificate
      SatInstance := SatInstance
      SatAssignment := SatAssignment
      instanceSize := instanceSize
      certificateSize := certificateSize
      satSize := satSize
      language := language
      verifier := verifier
      verifierTime := verifierTime
      assignmentBits := assignmentBits
      witnessTail := witnessTail
      witness := witness
      encode := encode
      reductionTime := reductionTime
      satEval := satEval
      witnessTail_eq := witnessTail_eq
      verifier_complete := @verifier_complete
      verifier_sound := @verifier_sound
      verifier_poly := verifier_poly
      witness_accepts := witness_accepts
      sat_sound := @sat_sound
      reduction_poly := reduction_poly }
  have hbase := paper_block_foldsat_np_complete D
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [D, BlockFoldsatNpCompleteData.inNP] using hbase.1
  · simpa [D, BlockFoldsatNpCompleteData.satKarpReduction, BlockFoldsatNpCompleteData.satLanguage]
      using hbase.2.1
  · intro φ a
    rw [witnessTail_eq]
    simp
  · intro φ
    exact (Fintype.card_congr (Equiv.ofBijective
      (fun a : {a : SatAssignment φ // satEval φ a = true} =>
        (⟨witness φ a.1, witness_accepts φ a.1 a.2⟩ :
          {cert : Certificate // verifier (encode φ) cert = true}))
      (witness_bijective φ))).symm

end Omega.Folding
