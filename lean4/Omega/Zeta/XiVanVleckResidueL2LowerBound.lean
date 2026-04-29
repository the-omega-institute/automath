import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete one-pole Van Vleck residue data. The real pole part is fixed to `0`, the imaginary
part is the positive parameter `imagPole`, and the residue moment constraint becomes
`-imagPole * Im(r) = -1`. -/
structure XiVanVleckResidueL2LowerBoundData where
  imagPole : ℝ
  himagPole : 0 < imagPole

namespace XiVanVleckResidueL2LowerBoundData

/-- Quadratic residue energy. -/
def energy (_D : XiVanVleckResidueL2LowerBoundData) (rePart imPart : ℝ) : ℝ :=
  rePart ^ 2 + imPart ^ 2

/-- The real moment vanishes and the first nontrivial Van Vleck moment is normalized to `-1`. -/
def admissible (D : XiVanVleckResidueL2LowerBoundData) (rePart imPart : ℝ) : Prop :=
  rePart = 0 ∧ -D.imagPole * imPart = -1

/-- The sharp lower bound from the normalized one-pole model. -/
def lowerBound (D : XiVanVleckResidueL2LowerBoundData) : ℝ :=
  1 / D.imagPole ^ 2

/-- The unique minimizer forced by the two linear constraints. -/
def minimizerRe (_D : XiVanVleckResidueL2LowerBoundData) : ℝ :=
  0

/-- The unique minimizer forced by the two linear constraints. -/
def minimizerIm (D : XiVanVleckResidueL2LowerBoundData) : ℝ :=
  1 / D.imagPole

def energyLowerBound (D : XiVanVleckResidueL2LowerBoundData) : Prop :=
  ∀ rePart imPart, D.admissible rePart imPart → D.lowerBound ≤ D.energy rePart imPart

def uniqueMinimizerFormula (D : XiVanVleckResidueL2LowerBoundData) : Prop :=
  D.admissible D.minimizerRe D.minimizerIm ∧
    D.energy D.minimizerRe D.minimizerIm = D.lowerBound ∧
      ∀ rePart imPart,
        D.admissible rePart imPart →
          D.energy rePart imPart = D.lowerBound →
            rePart = D.minimizerRe ∧ imPart = D.minimizerIm

lemma imagPole_ne (D : XiVanVleckResidueL2LowerBoundData) : D.imagPole ≠ 0 :=
  ne_of_gt D.himagPole

lemma admissible_minimizer (D : XiVanVleckResidueL2LowerBoundData) :
    D.admissible D.minimizerRe D.minimizerIm := by
  refine ⟨rfl, ?_⟩
  have hmul : D.imagPole * (1 / D.imagPole) = 1 := by
    field_simp [D.imagPole_ne]
  simpa [minimizerIm] using congrArg Neg.neg hmul

lemma energy_minimizer (D : XiVanVleckResidueL2LowerBoundData) :
    D.energy D.minimizerRe D.minimizerIm = D.lowerBound := by
  unfold energy lowerBound minimizerRe minimizerIm
  field_simp [D.imagPole_ne]
  ring

lemma imagPart_eq_minimizer
    (D : XiVanVleckResidueL2LowerBoundData) {imPart : ℝ}
    (hMoment : -D.imagPole * imPart = -1) :
    imPart = D.minimizerIm := by
  have hmul : D.imagPole * imPart = 1 := by nlinarith
  apply (eq_div_iff D.imagPole_ne).2
  simpa [minimizerIm, mul_comm] using hmul

lemma energyLowerBound_true (D : XiVanVleckResidueL2LowerBoundData) :
    D.energyLowerBound := by
  intro rePart imPart h
  rcases h with ⟨hre, hMoment⟩
  have him : imPart = D.minimizerIm := D.imagPart_eq_minimizer hMoment
  have hEnergy :
      D.energy 0 D.minimizerIm = D.lowerBound := by
    simpa [minimizerRe] using D.energy_minimizer
  rw [hre, him, hEnergy]

lemma uniqueMinimizerFormula_true (D : XiVanVleckResidueL2LowerBoundData) :
    D.uniqueMinimizerFormula := by
  refine ⟨D.admissible_minimizer, D.energy_minimizer, ?_⟩
  intro rePart imPart h hEq
  rcases h with ⟨hre, hMoment⟩
  exact ⟨hre, D.imagPart_eq_minimizer hMoment⟩

end XiVanVleckResidueL2LowerBoundData

open XiVanVleckResidueL2LowerBoundData

/-- Paper label: `thm:xi-vanvleck-residue-l2-lower-bound`. -/
theorem paper_xi_vanvleck_residue_l2_lower_bound_one_pole
    (D : XiVanVleckResidueL2LowerBoundData) :
    D.energyLowerBound ∧ D.uniqueMinimizerFormula := by
  exact ⟨D.energyLowerBound_true, D.uniqueMinimizerFormula_true⟩

end

end Omega.Zeta
