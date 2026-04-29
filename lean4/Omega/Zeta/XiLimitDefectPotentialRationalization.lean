import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Complex

/-- One finite defect packet with center `γ`, offset `δ ∈ (0,1)`, and multiplicity `m`. -/
structure XiLimitDefectPacket where
  γ : ℝ
  δ : Set.Ioo (0 : ℝ) 1
  m : ℕ

/-- The elementary quadratic factor appearing in the real rationalized product. -/
noncomputable def xiRealQuadraticFactor (P : XiLimitDefectPacket) (x : ℝ) : ℝ :=
  ((x - P.γ) ^ 2 + (1 - P.δ.1) ^ 2) / ((x - P.γ) ^ 2 + (1 + P.δ.1) ^ 2)

/-- The logarithmic kernel whose exponential produces the quadratic factor. -/
noncomputable def xiPacketKernel (P : XiLimitDefectPacket) (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (xiRealQuadraticFactor P x)

/-- The finite defect potential. -/
noncomputable def xiLimitDefectPotential : List XiLimitDefectPacket → ℝ → ℝ
  | [], _ => 0
  | P :: Ps, x => (P.m : ℝ) * xiPacketKernel P x + xiLimitDefectPotential Ps x

/-- The explicit real product formula. -/
noncomputable def xiExplicitProductFormula : List XiLimitDefectPacket → ℝ → ℝ
  | [], _ => 1
  | P :: Ps, x => xiRealQuadraticFactor P x ^ P.m * xiExplicitProductFormula Ps x

/-- The same product interpreted over `ℂ`, giving the rational extension. -/
noncomputable def xiComplexQuadraticFactor (P : XiLimitDefectPacket) (z : ℂ) : ℂ :=
  ((z - (P.γ : ℂ)) ^ 2 + ((1 - P.δ.1 : ℝ) : ℂ) ^ 2) /
    ((z - (P.γ : ℂ)) ^ 2 + ((1 + P.δ.1 : ℝ) : ℂ) ^ 2)

/-- The complex rational extension of the explicit product. -/
noncomputable def xiComplexProductFormula : List XiLimitDefectPacket → ℂ → ℂ
  | [], _ => 1
  | P :: Ps, z => xiComplexQuadraticFactor P z ^ P.m * xiComplexProductFormula Ps z

/-- The zero location attached to one packet. -/
def xiZeroLocation (P : XiLimitDefectPacket) : ℝ × ℝ :=
  (P.γ, 1 - P.δ.1)

/-- The pole location attached to one packet. -/
def xiPoleLocation (P : XiLimitDefectPacket) : ℝ × ℝ :=
  (P.γ, 1 + P.δ.1)

/-- The original packet parameter data. -/
def xiPacketParameterData (P : XiLimitDefectPacket) : ℝ × ℝ × ℕ :=
  (P.γ, P.δ.1, P.m)

/-- Recovering the parameters from the zero/pole heights. -/
noncomputable def xiRecoveredParameterData (P : XiLimitDefectPacket) : ℝ × ℝ × ℕ :=
  (P.γ, ((xiPoleLocation P).2 - (xiZeroLocation P).2) / 2, P.m)

/-- The zero/pole data recovers the original packet parameters. -/
def xiParametersRecoverable (packets : List XiLimitDefectPacket) : Prop :=
  packets.map xiRecoveredParameterData = packets.map xiPacketParameterData

lemma xiRealQuadraticFactor_pos (P : XiLimitDefectPacket) (x : ℝ) :
    0 < xiRealQuadraticFactor P x := by
  unfold xiRealQuadraticFactor
  have hminus : 0 < 1 - P.δ.1 := sub_pos.mpr P.δ.2.2
  have hplus : 0 < 1 + P.δ.1 := by linarith [P.δ.2.1]
  have hnum : 0 < (x - P.γ) ^ 2 + (1 - P.δ.1) ^ 2 := by
    have hsquare : 0 < (1 - P.δ.1) ^ 2 := sq_pos_of_pos hminus
    nlinarith [sq_nonneg (x - P.γ)]
  have hden : 0 < (x - P.γ) ^ 2 + (1 + P.δ.1) ^ 2 := by
    have hsquare : 0 < (1 + P.δ.1) ^ 2 := sq_pos_of_pos hplus
    nlinarith [sq_nonneg (x - P.γ)]
  exact div_pos hnum hden

lemma xi_single_packet_explicit_formula (P : XiLimitDefectPacket) (x : ℝ) :
    Real.exp (-2 * ((P.m : ℝ) * xiPacketKernel P x)) = xiRealQuadraticFactor P x ^ P.m := by
  have hfactor : 0 < xiRealQuadraticFactor P x := xiRealQuadraticFactor_pos P x
  unfold xiPacketKernel
  calc
    Real.exp (-2 * ((P.m : ℝ) * (-(1 / 2 : ℝ) * Real.log (xiRealQuadraticFactor P x))))
        = Real.exp ((P.m : ℝ) * Real.log (xiRealQuadraticFactor P x)) := by
            ring_nf
    _ = Real.exp (Real.log (xiRealQuadraticFactor P x)) ^ P.m := by
          rw [Real.exp_nat_mul]
    _ = xiRealQuadraticFactor P x ^ P.m := by
          rw [Real.exp_log hfactor]

lemma xi_explicit_product_formula (packets : List XiLimitDefectPacket) :
    ∀ x : ℝ, Real.exp (-2 * xiLimitDefectPotential packets x) = xiExplicitProductFormula packets x := by
  induction packets with
  | nil =>
      intro x
      simp [xiLimitDefectPotential, xiExplicitProductFormula]
  | cons P Ps ih =>
      intro x
      calc
        Real.exp (-2 * xiLimitDefectPotential (P :: Ps) x)
            = Real.exp (-2 * ((P.m : ℝ) * xiPacketKernel P x + xiLimitDefectPotential Ps x)) := by
                rfl
        _ = Real.exp (-2 * ((P.m : ℝ) * xiPacketKernel P x)) *
              Real.exp (-2 * xiLimitDefectPotential Ps x) := by
                rw [show -2 * ((P.m : ℝ) * xiPacketKernel P x + xiLimitDefectPotential Ps x) =
                    (-2 * ((P.m : ℝ) * xiPacketKernel P x)) +
                      (-2 * xiLimitDefectPotential Ps x) by ring]
                rw [Real.exp_add]
        _ = xiRealQuadraticFactor P x ^ P.m * xiExplicitProductFormula Ps x := by
              rw [xi_single_packet_explicit_formula, ih x]
        _ = xiExplicitProductFormula (P :: Ps) x := by
              rfl

lemma xi_complex_quadraticFactor_on_real (P : XiLimitDefectPacket) (x : ℝ) :
    xiComplexQuadraticFactor P x = (xiRealQuadraticFactor P x : ℂ) := by
  simp [xiComplexQuadraticFactor, xiRealQuadraticFactor]

lemma xi_rational_extension (packets : List XiLimitDefectPacket) :
    ∀ x : ℝ, xiComplexProductFormula packets x = (xiExplicitProductFormula packets x : ℂ) := by
  induction packets with
  | nil =>
      intro x
      simp [xiComplexProductFormula, xiExplicitProductFormula]
  | cons P Ps ih =>
      intro x
      simp [xiComplexProductFormula, xiExplicitProductFormula, ih x,
        xi_complex_quadraticFactor_on_real]

lemma xi_recoveredParameterData_eq (P : XiLimitDefectPacket) :
    xiRecoveredParameterData P = xiPacketParameterData P := by
  cases P with
  | mk γ δ m =>
      cases δ with
      | mk δ hδ =>
          simp [xiRecoveredParameterData, xiPacketParameterData, xiZeroLocation, xiPoleLocation]

lemma xi_parameters_recoverable (packets : List XiLimitDefectPacket) :
    xiParametersRecoverable packets := by
  induction packets with
  | nil =>
      simp [xiParametersRecoverable]
  | cons P Ps _ =>
      simp [xiParametersRecoverable, xi_recoveredParameterData_eq]

/-- Finite defect rationalization package: exponentiating the concrete kernel sum gives the
explicit quadratic product, the same formula extends verbatim to `ℂ`, and the zero/pole heights
recover the original defect parameters.
    prop:xi-limit-defect-potential-rationalization -/
theorem paper_xi_limit_defect_potential_rationalization (packets : List XiLimitDefectPacket) :
    (∀ x : ℝ, Real.exp (-2 * xiLimitDefectPotential packets x) = xiExplicitProductFormula packets x) ∧
      (∀ x : ℝ, xiComplexProductFormula packets x = (xiExplicitProductFormula packets x : ℂ)) ∧
      xiParametersRecoverable packets := by
  exact ⟨xi_explicit_product_formula packets, xi_rational_extension packets,
    xi_parameters_recoverable packets⟩

end Omega.Zeta
