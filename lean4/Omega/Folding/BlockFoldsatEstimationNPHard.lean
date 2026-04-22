import Mathlib.Tactic
import Omega.Folding.BlockFoldsatNpComplete
import Omega.SPG.PolytimeCompleteInvariantImpliesPEqualsNP

namespace Omega.Folding

/-- Threshold classifier obtained from an approximation to the Block--FoldSAT acceptance rate and
the computable fiber denominator. -/
def block_foldsat_estimation_np_hard_threshold_decide
    (D : BlockFoldsatNpCompleteData) (dm : D.SatInstance → ℕ) (approx : D.SatInstance → ℚ) :
    D.SatInstance → Bool :=
  fun φ => decide (1 / (((2 * dm φ : ℕ) : ℚ)) < approx φ)

/-- Concrete statement for the inverse-denominator gap used in the paper's hardness reduction. -/
def block_foldsat_estimation_np_hard_statement (D : BlockFoldsatNpCompleteData) : Prop :=
  D.npComplete ∧
    ∀ (dm : D.SatInstance → ℕ) (approx : D.SatInstance → ℚ),
      Omega.SPG.PolynomialTimeMap dm →
      Omega.SPG.PolynomialTimeMap approx →
      (∀ φ, (¬ ∃ a : D.SatAssignment φ, D.satEval φ a = true) →
        approx φ < 1 / (((2 * dm φ : ℕ) : ℚ))) →
      (∀ φ, (∃ a : D.SatAssignment φ, D.satEval φ a = true) →
        1 / (((2 * dm φ : ℕ) : ℚ)) < approx φ) →
      Omega.SPG.PolytimeDecidable (fun φ => ∃ a : D.SatAssignment φ, D.satEval φ a = true) ∧
        Omega.SPG.PEqualsNP (fun φ => ∃ a : D.SatAssignment φ, D.satEval φ a = true)

/-- Paper label: `prop:block-foldsat-estimation-np-hard`. -/
def paper_block_foldsat_estimation_np_hard (D : Omega.Folding.BlockFoldsatNpCompleteData) :
    Prop :=
  block_foldsat_estimation_np_hard_statement D

theorem block_foldsat_estimation_np_hard_certified (D : BlockFoldsatNpCompleteData) :
    paper_block_foldsat_estimation_np_hard D := by
  refine ⟨(paper_block_foldsat_np_complete D).2.2, ?_⟩
  intro dm approx _ _ hUnsat hSat
  let decideSat :=
    block_foldsat_estimation_np_hard_threshold_decide D dm approx
  have hSpec :
      ∀ φ,
        decideSat φ = true ↔ ∃ a : D.SatAssignment φ, D.satEval φ a = true := by
    intro φ
    by_cases hφ : ∃ a : D.SatAssignment φ, D.satEval φ a = true
    · constructor
      · intro _
        exact hφ
      · intro _
        have hlt : 1 / (((2 * dm φ : ℕ) : ℚ)) < approx φ := hSat φ hφ
        simpa [decideSat, block_foldsat_estimation_np_hard_threshold_decide] using hlt
    · constructor
      · intro hDecide
        have hlt : 1 / (((2 * dm φ : ℕ) : ℚ)) < approx φ := by
          simpa [decideSat, block_foldsat_estimation_np_hard_threshold_decide] using hDecide
        have hupper : approx φ < 1 / (((2 * dm φ : ℕ) : ℚ)) := hUnsat φ hφ
        linarith
      · intro hSatWitness
        exact False.elim (hφ hSatWitness)
  have hSatInP :
      Omega.SPG.PolytimeDecidable (fun φ => ∃ a : D.SatAssignment φ, D.satEval φ a = true) :=
    ⟨decideSat, trivial, hSpec⟩
  exact ⟨hSatInP, ⟨Omega.SPG.complement_polytime_decidable hSatInP, hSatInP⟩⟩

end Omega.Folding
