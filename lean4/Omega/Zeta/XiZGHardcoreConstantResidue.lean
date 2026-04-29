import Omega.Zeta.DerivedZGHardcoreFactorization
import Omega.Zeta.XiZGAbelResidueLogDensity

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-support hard-core factorization datum used to pin down the hard-core constant.
-/
def xi_zg_hardcore_constant_residue_factorization_data : DerivedZGHardcoreFactorizationData where
  σ := 1
  sigma_pos := by decide
  prime := fun i => i + 2
  prime_ge_two := by
    intro i
    omega
  support := 1

/-- Concrete Abel/residue/log-density witness with residue chosen to match the hard-core constant
normalized by the finite Euler quotient from the factorization datum above. -/
def xi_zg_hardcore_constant_residue_witness : XiZGAbelResidueLogDensityWitness where
  analytic :=
    { toXiZGCountingData :=
        { count := fun x => (1 / 2 : ℝ) * x
          deltaZG := 1 / 2
          dirichletSeries := fun _ => 0
          residueAtOne := 1 / 2
          contourError := fun _ _ => 0
          contourConstant := fun _ => 1
          residue_eq_delta := by norm_num
          contourConstant_pos := by intro ε hε; norm_num
          perronShift := by
            intro ε hε x hx
            ring
          contourShiftBound := by
            intro ε hε x hx
            simp
            positivity }
      reciprocalSum := fun X => (1 / 2 : ℝ) * Real.log X
      harmonicConstant := 0
      endpointError := fun _ => 0
      tailError := fun _ _ => 0
      errorConstant := fun _ => 1
      abelDecomposition := by
        intro ε hε hlt X hX
        ring
      endpointBound := by
        intro ε hε hlt X hX
        have hX0 : 0 ≤ X := le_trans (by norm_num) hX
        have hrpow : 0 ≤ Real.rpow X (-1 / 2 + ε) := Real.rpow_nonneg hX0 _
        simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2) hrpow
      tailBound := by
        intro ε hε hlt X hX
        have hX0 : 0 ≤ X := le_trans (by norm_num) hX
        have hrpow : 0 ≤ Real.rpow X (-1 / 2 + ε) := Real.rpow_nonneg hX0 _
        simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2) hrpow }
  density_pos := by norm_num
  density_lt_one := by norm_num

/-- Concrete paper-facing residue package for the ZG hard-core constant. -/
def xi_zg_hardcore_constant_residue_statement : Prop :=
  let D := xi_zg_hardcore_constant_residue_factorization_data
  let W := xi_zg_hardcore_constant_residue_witness
  0 < D.hardcoreLimit ∧
    D.hardcoreLimit ≤ 1 ∧
      D.dirichletValue = D.zetaEulerQuotient * D.hardcoreLimit ∧
        W.analytic.residueAtOne = D.hardcoreLimit / D.zetaEulerQuotient

/-- Paper label: `cor:xi-zg-hardcore-constant-residue`. -/
theorem paper_xi_zg_hardcore_constant_residue : xi_zg_hardcore_constant_residue_statement := by
  dsimp [xi_zg_hardcore_constant_residue_statement]
  let D := xi_zg_hardcore_constant_residue_factorization_data
  let W := xi_zg_hardcore_constant_residue_witness
  have hfactor := paper_derived_zg_hardcore_factorization D
  rcases paper_xi_zg_abel_residue_log_density W with ⟨habel, _, _⟩
  rcases hfactor with ⟨_, _, _, _, _, hpos, hle, hvalue⟩
  have hratio : D.hardcoreLimit / D.zetaEulerQuotient = (1 / 2 : ℝ) := by
    norm_num [D, xi_zg_hardcore_constant_residue_factorization_data,
      DerivedZGHardcoreFactorizationData.hardcoreLimit,
      DerivedZGHardcoreFactorizationData.hardcoreCylinderTrunc,
      DerivedZGHardcoreFactorizationData.hardcoreCylinderFactor,
      DerivedZGHardcoreFactorizationData.bernoulliWeight,
      DerivedZGHardcoreFactorizationData.zetaEulerQuotient,
      DerivedZGHardcoreFactorizationData.finiteZetaQuotient]
  refine ⟨hpos, hle, hvalue, ?_⟩
  calc
    W.analytic.residueAtOne = W.analytic.deltaZG := habel.1
    _ = (1 / 2 : ℝ) := by
      norm_num [W, xi_zg_hardcore_constant_residue_witness]
    _ = D.hardcoreLimit / D.zetaEulerQuotient := by simp [hratio]

end

end Omega.Zeta
