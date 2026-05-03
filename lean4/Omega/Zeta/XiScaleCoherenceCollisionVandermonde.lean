import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the scale-coherence collision package.  The fields record the positive
Hankel leading constant, the collision Vandermonde product, and the normalized determinant
expansion after the kernel Taylor expansion has been bundled into the coefficient data. -/
structure xi_scale_coherence_collision_vandermonde_data where
  xi_scale_coherence_collision_vandermonde_kappa : ℕ
  xi_scale_coherence_collision_vandermonde_epsilon : ℝ
  xi_scale_coherence_collision_vandermonde_epsilonPower : ℝ
  xi_scale_coherence_collision_vandermonde_leadingConstant : ℝ
  xi_scale_coherence_collision_vandermonde_pairwiseProduct : ℝ
  xi_scale_coherence_collision_vandermonde_remainder : ℝ
  xi_scale_coherence_collision_vandermonde_gramDet : ℝ
  xi_scale_coherence_collision_vandermonde_logVolumePotential : ℝ
  xi_scale_coherence_collision_vandermonde_leadingConstant_pos :
    0 < xi_scale_coherence_collision_vandermonde_leadingConstant
  xi_scale_coherence_collision_vandermonde_pairwiseProduct_pos :
    0 < xi_scale_coherence_collision_vandermonde_pairwiseProduct
  xi_scale_coherence_collision_vandermonde_epsilonPower_pos :
    0 < xi_scale_coherence_collision_vandermonde_epsilonPower
  xi_scale_coherence_collision_vandermonde_remainder_pos :
    0 < 1 + xi_scale_coherence_collision_vandermonde_remainder
  xi_scale_coherence_collision_vandermonde_epsilonPower_log :
    Real.log xi_scale_coherence_collision_vandermonde_epsilonPower =
      (xi_scale_coherence_collision_vandermonde_kappa *
          (xi_scale_coherence_collision_vandermonde_kappa - 1) : ℝ) *
        Real.log xi_scale_coherence_collision_vandermonde_epsilon
  xi_scale_coherence_collision_vandermonde_gramDet_eq :
    xi_scale_coherence_collision_vandermonde_gramDet =
      xi_scale_coherence_collision_vandermonde_leadingConstant *
        xi_scale_coherence_collision_vandermonde_epsilonPower *
          xi_scale_coherence_collision_vandermonde_pairwiseProduct *
            (1 + xi_scale_coherence_collision_vandermonde_remainder)
  xi_scale_coherence_collision_vandermonde_logVolume_eq :
    xi_scale_coherence_collision_vandermonde_logVolumePotential =
      -Real.log xi_scale_coherence_collision_vandermonde_gramDet

/-- The determinant leading term after the confluent-Vandermonde construction. -/
def xi_scale_coherence_collision_vandermonde_determinantLeadingTerm
    (D : xi_scale_coherence_collision_vandermonde_data) : Prop :=
  D.xi_scale_coherence_collision_vandermonde_gramDet =
    D.xi_scale_coherence_collision_vandermonde_leadingConstant *
      D.xi_scale_coherence_collision_vandermonde_epsilonPower *
        D.xi_scale_coherence_collision_vandermonde_pairwiseProduct *
          (1 + D.xi_scale_coherence_collision_vandermonde_remainder)

/-- The logarithmic volume expansion obtained from the positive leading constant and the
collision product. -/
def xi_scale_coherence_collision_vandermonde_logVolumeAsymptotic
    (D : xi_scale_coherence_collision_vandermonde_data) : Prop :=
  D.xi_scale_coherence_collision_vandermonde_logVolumePotential =
    -Real.log D.xi_scale_coherence_collision_vandermonde_leadingConstant -
      (D.xi_scale_coherence_collision_vandermonde_kappa *
          (D.xi_scale_coherence_collision_vandermonde_kappa - 1) : ℝ) *
        Real.log D.xi_scale_coherence_collision_vandermonde_epsilon -
      Real.log D.xi_scale_coherence_collision_vandermonde_pairwiseProduct -
      Real.log (1 + D.xi_scale_coherence_collision_vandermonde_remainder)

/-- Concrete statement of the scale-coherence collision Vandermonde law. -/
def xi_scale_coherence_collision_vandermonde_statement
    (D : xi_scale_coherence_collision_vandermonde_data) : Prop :=
  xi_scale_coherence_collision_vandermonde_determinantLeadingTerm D ∧
    xi_scale_coherence_collision_vandermonde_logVolumeAsymptotic D ∧
    0 < D.xi_scale_coherence_collision_vandermonde_leadingConstant ∧
    0 < D.xi_scale_coherence_collision_vandermonde_pairwiseProduct

/-- Paper label: `prop:xi-scale-coherence-collision-vandermonde`. -/
theorem paper_xi_scale_coherence_collision_vandermonde
    (D : xi_scale_coherence_collision_vandermonde_data) :
    xi_scale_coherence_collision_vandermonde_statement D := by
  refine ⟨D.xi_scale_coherence_collision_vandermonde_gramDet_eq, ?_,
    D.xi_scale_coherence_collision_vandermonde_leadingConstant_pos,
    D.xi_scale_coherence_collision_vandermonde_pairwiseProduct_pos⟩
  dsimp [xi_scale_coherence_collision_vandermonde_logVolumeAsymptotic]
  have hlog :
      Real.log
          (D.xi_scale_coherence_collision_vandermonde_leadingConstant *
            D.xi_scale_coherence_collision_vandermonde_epsilonPower *
              D.xi_scale_coherence_collision_vandermonde_pairwiseProduct *
                (1 + D.xi_scale_coherence_collision_vandermonde_remainder)) =
        Real.log D.xi_scale_coherence_collision_vandermonde_leadingConstant +
          (D.xi_scale_coherence_collision_vandermonde_kappa *
              (D.xi_scale_coherence_collision_vandermonde_kappa - 1) : ℝ) *
            Real.log D.xi_scale_coherence_collision_vandermonde_epsilon +
          Real.log D.xi_scale_coherence_collision_vandermonde_pairwiseProduct +
          Real.log (1 + D.xi_scale_coherence_collision_vandermonde_remainder) := by
    rw [Real.log_mul
      (mul_pos
        (mul_pos D.xi_scale_coherence_collision_vandermonde_leadingConstant_pos
          D.xi_scale_coherence_collision_vandermonde_epsilonPower_pos)
        D.xi_scale_coherence_collision_vandermonde_pairwiseProduct_pos).ne'
      D.xi_scale_coherence_collision_vandermonde_remainder_pos.ne']
    rw [Real.log_mul
      (mul_pos D.xi_scale_coherence_collision_vandermonde_leadingConstant_pos
        D.xi_scale_coherence_collision_vandermonde_epsilonPower_pos).ne'
      D.xi_scale_coherence_collision_vandermonde_pairwiseProduct_pos.ne']
    rw [Real.log_mul
      D.xi_scale_coherence_collision_vandermonde_leadingConstant_pos.ne'
      D.xi_scale_coherence_collision_vandermonde_epsilonPower_pos.ne']
    rw [D.xi_scale_coherence_collision_vandermonde_epsilonPower_log]
  calc
    D.xi_scale_coherence_collision_vandermonde_logVolumePotential =
        -Real.log
          (D.xi_scale_coherence_collision_vandermonde_leadingConstant *
            D.xi_scale_coherence_collision_vandermonde_epsilonPower *
              D.xi_scale_coherence_collision_vandermonde_pairwiseProduct *
                (1 + D.xi_scale_coherence_collision_vandermonde_remainder)) := by
          rw [D.xi_scale_coherence_collision_vandermonde_logVolume_eq,
            D.xi_scale_coherence_collision_vandermonde_gramDet_eq]
    _ =
        -Real.log D.xi_scale_coherence_collision_vandermonde_leadingConstant -
          (D.xi_scale_coherence_collision_vandermonde_kappa *
              (D.xi_scale_coherence_collision_vandermonde_kappa - 1) : ℝ) *
            Real.log D.xi_scale_coherence_collision_vandermonde_epsilon -
          Real.log D.xi_scale_coherence_collision_vandermonde_pairwiseProduct -
          Real.log (1 + D.xi_scale_coherence_collision_vandermonde_remainder) := by
          rw [hlog]
          ring

end

end Omega.Zeta
