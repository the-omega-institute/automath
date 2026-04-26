import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.POM

/-- A simple sharp asymptotic wrapper: the quotient tends to `1`. -/
def SharpAsymptotic (f g : ℕ → ℝ) : Prop :=
  Tendsto (fun L => f L / g L) atTop (𝓝 1)

/-- Concrete zero/one-defect data for the mod-`3` multiplicity-composition layer comparison. -/
structure MultiplicityCompositionMod3ZeroOneDefectSharpData where
  probZero : ℕ → ℝ
  probOne : ℕ → ℝ
  probLeOne : ℕ → ℝ
  lambda0 : ℝ
  lambda : ℝ
  mu0 : ℝ
  mu : ℝ
  badResidueWeight : ℝ
  lambda0_ne : lambda0 ≠ 0
  lambda_ne : lambda ≠ 0
  mu0_ne : mu0 ≠ 0
  mu_ne : mu ≠ 0
  badResidueWeight_ne : badResidueWeight ≠ 0
  probLeOne_eq : ∀ L, probLeOne L = probZero L + probOne L
  probOne_pos : ∀ L, 0 < probOne L
  zeroSharp :
    SharpAsymptotic probZero
      (fun L => (mu / mu0) * (lambda0 / lambda) ^ L)
  oneSharp :
    SharpAsymptotic probOne
      (fun L => (mu * badResidueWeight / mu0 ^ 2) * (L : ℝ) * (lambda0 / lambda) ^ L)
  zeroOverOne :
    Tendsto (fun L => probZero L / probOne L) atTop (𝓝 0)
  zeroMainDominated :
    Tendsto
      (fun L =>
        ((mu / mu0) * (lambda0 / lambda) ^ (L + 1)) /
          ((mu * badResidueWeight / mu0 ^ 2) * ((L + 1 : ℕ) : ℝ) * (lambda0 / lambda) ^ (L + 1)))
      atTop (𝓝 0)

namespace MultiplicityCompositionMod3ZeroOneDefectSharpData

noncomputable def decayRatio (D : MultiplicityCompositionMod3ZeroOneDefectSharpData) : ℝ :=
  D.lambda0 / D.lambda

noncomputable def zeroCoefficient (D : MultiplicityCompositionMod3ZeroOneDefectSharpData) : ℝ :=
  D.mu / D.mu0

noncomputable def oneCoefficient (D : MultiplicityCompositionMod3ZeroOneDefectSharpData) : ℝ :=
  D.mu * D.badResidueWeight / D.mu0 ^ 2

noncomputable def zeroMainTerm (D : MultiplicityCompositionMod3ZeroOneDefectSharpData)
    (L : ℕ) : ℝ :=
  D.zeroCoefficient * D.decayRatio ^ L

noncomputable def oneMainTerm (D : MultiplicityCompositionMod3ZeroOneDefectSharpData)
    (L : ℕ) : ℝ :=
  D.oneCoefficient * (L : ℝ) * D.decayRatio ^ L

/-- The sharp zero-defect and one-defect asymptotics, together with the domination of the
`A_L = 1` layer over the `A_L = 0` layer. -/
def zeroOneDefectSharp (D : MultiplicityCompositionMod3ZeroOneDefectSharpData) : Prop :=
  SharpAsymptotic D.probZero D.zeroMainTerm ∧
    SharpAsymptotic D.probOne D.oneMainTerm ∧
    SharpAsymptotic D.probLeOne D.probOne ∧
    Tendsto (fun L => D.zeroMainTerm (L + 1) / D.oneMainTerm (L + 1)) atTop (𝓝 0)

lemma oneCoefficient_ne (D : MultiplicityCompositionMod3ZeroOneDefectSharpData) :
    D.oneCoefficient ≠ 0 := by
  unfold oneCoefficient
  exact div_ne_zero (mul_ne_zero D.mu_ne D.badResidueWeight_ne) (pow_ne_zero 2 D.mu0_ne)

end MultiplicityCompositionMod3ZeroOneDefectSharpData

open MultiplicityCompositionMod3ZeroOneDefectSharpData

/-- Paper label: `thm:pom-multiplicity-composition-mod3-zero-one-defect-sharp`. -/
theorem paper_pom_multiplicity_composition_mod3_zero_one_defect_sharp
    (D : MultiplicityCompositionMod3ZeroOneDefectSharpData) : D.zeroOneDefectSharp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [SharpAsymptotic, zeroMainTerm, zeroCoefficient, decayRatio] using D.zeroSharp
  · simpa [SharpAsymptotic, oneMainTerm, oneCoefficient, decayRatio] using D.oneSharp
  · change Tendsto (fun L => D.probLeOne L / D.probOne L) atTop (𝓝 1)
    have hEq :
        (fun L => D.probLeOne L / D.probOne L) =
          fun L => D.probZero L / D.probOne L + 1 := by
      funext L
      rw [D.probLeOne_eq L]
      have hpo : D.probOne L ≠ 0 := ne_of_gt (D.probOne_pos L)
      field_simp [hpo]
    rw [hEq]
    simpa using D.zeroOverOne.add tendsto_const_nhds
  · simpa [zeroMainTerm, oneMainTerm, zeroCoefficient, oneCoefficient, decayRatio] using
      D.zeroMainDominated

end Omega.POM
