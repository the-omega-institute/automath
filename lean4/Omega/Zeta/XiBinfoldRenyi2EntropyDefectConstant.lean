import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.Folding.KilloFoldRenyi2UniformityGap

namespace Omega.Zeta

open Omega.Folding

/-- Concrete scale parameter for the bin-fold Rényi-`2` entropy-defect wrapper. -/
structure XiBinfoldRenyi2EntropyDefectConstantData where
  m : ℕ

namespace XiBinfoldRenyi2EntropyDefectConstantData

/-- Natural-log Rényi-`2` entropy `H₂(μ_m) = -log Col_m`. -/
noncomputable def renyi2EntropyNat (D : XiBinfoldRenyi2EntropyDefectConstantData) : ℝ :=
  -Real.log (killoFoldCollisionProbability D.m)

/-- Base-`2` logarithm. -/
noncomputable def log2 (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

/-- Bit-valued Rényi-`2` entropy `H₂^{(2)}(μ_m) = -log₂ Col_m`. -/
noncomputable def renyi2EntropyBit (D : XiBinfoldRenyi2EntropyDefectConstantData) : ℝ :=
  -log2 (killoFoldCollisionProbability D.m)

/-- The natural-log entropy defect `log F_{m+2} - H₂(μ_m)`. -/
noncomputable def natGap (D : XiBinfoldRenyi2EntropyDefectConstantData) : ℝ :=
  Real.log (killoFoldModulus D.m) - D.renyi2EntropyNat

/-- The bit-valued entropy defect `log₂ F_{m+2} - H₂^{(2)}(μ_m)`. -/
noncomputable def bitGap (D : XiBinfoldRenyi2EntropyDefectConstantData) : ℝ :=
  log2 (killoFoldModulus D.m) - D.renyi2EntropyBit

/-- The concrete nat-scale lower bound supplied by the already formalized Rényi-`2` obstruction. -/
noncomputable def natLowerBound (D : XiBinfoldRenyi2EntropyDefectConstantData) : Prop :=
  D.natGap = killoFoldRenyiTwoDivergence D.m ∧ killoFoldUniformityGap ≤ D.natGap

/-- The same lower bound rewritten in bits by dividing through by `log 2`. -/
noncomputable def bitLowerBound (D : XiBinfoldRenyi2EntropyDefectConstantData) : Prop :=
  D.bitGap = killoFoldRenyiTwoDivergence D.m / Real.log 2 ∧
    killoFoldUniformityGap / Real.log 2 ≤ D.bitGap

end XiBinfoldRenyi2EntropyDefectConstantData

open XiBinfoldRenyi2EntropyDefectConstantData

/-- The bin-fold Rényi-`2` obstruction can be rewritten as the entropy defect
`log F_{m+2} - H₂(μ_m)`, and the same lower bound converts from nats to bits by dividing by
`log 2`. -/
theorem paper_xi_binfold_renyi2_entropy_defect_constant
    (D : XiBinfoldRenyi2EntropyDefectConstantData) :
    And D.natLowerBound D.bitLowerBound := by
  have hFibPos : (0 : ℝ) < killoFoldModulus D.m := by
    exact_mod_cast Nat.fib_pos.mpr (by omega)
  have hColPos : (0 : ℝ) < killoFoldCollisionProbability D.m := by
    unfold killoFoldCollisionProbability killoFoldResonanceConstant
    positivity
  have hlog2_pos : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num)
  have hnat_eq :
      D.natGap = killoFoldRenyiTwoDivergence D.m := by
    unfold XiBinfoldRenyi2EntropyDefectConstantData.natGap
      XiBinfoldRenyi2EntropyDefectConstantData.renyi2EntropyNat
      killoFoldRenyiTwoDivergence
    rw [sub_neg_eq_add]
    rw [← Real.log_mul hFibPos.ne' hColPos.ne']
  have hgap_const : killoFoldRenyiTwoDivergence D.m = killoFoldUniformityGap := by
    have hmod : (killoFoldModulus D.m : ℝ) ≠ 0 := hFibPos.ne'
    simp [killoFoldRenyiTwoDivergence, killoFoldCollisionProbability, killoFoldUniformityGap, hmod,
      mul_left_comm, mul_comm]
  have hbit_eq_nat : D.bitGap = D.natGap / Real.log 2 := by
    unfold XiBinfoldRenyi2EntropyDefectConstantData.bitGap
      XiBinfoldRenyi2EntropyDefectConstantData.natGap
      XiBinfoldRenyi2EntropyDefectConstantData.renyi2EntropyBit
      XiBinfoldRenyi2EntropyDefectConstantData.renyi2EntropyNat
      XiBinfoldRenyi2EntropyDefectConstantData.log2
    field_simp [hlog2_pos.ne']
  have hbit_eq :
      D.bitGap = killoFoldRenyiTwoDivergence D.m / Real.log 2 := by
    rw [hbit_eq_nat, hnat_eq]
  refine ⟨?_, ?_⟩
  · refine ⟨hnat_eq, ?_⟩
    rw [hnat_eq, hgap_const]
  · refine ⟨hbit_eq, ?_⟩
    rw [hbit_eq, hgap_const]

end Omega.Zeta
