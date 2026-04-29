import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiComovingScanHankelRankDefect
import Omega.Zeta.XiScanMinSeparationLocalBilipschitz

namespace Omega.Zeta

/-- Concrete collision data for the separated `xi`-scan ill-posedness corollary. The separated
finite-defect package supplies the local bilipschitz constants, the Hankel/Vandermonde package
supplies the factorization and full-rank certificate, and the remaining scalar fields encode the
near-collision asymptotic `sep ∼ Δ * |γ_j - γ_k|` together with the resulting blow-up scale. -/
structure xi_scan_collision_illposedness_data (κ : ℕ) where
  localBilipschitz : xi_scan_min_separation_local_bilipschitz_data κ
  atomicMoment : XiFiniteAtomicMomentData κ
  collisionGap : ℝ
  collisionScale : ℝ
  illposednessScale : ℝ
  weights_nonzero : ∀ j : Fin κ, atomicMoment.weights j ≠ 0
  nodes_injective : Function.Injective atomicMoment.nodes
  collisionGap_pos : 0 < collisionGap
  collisionScale_pos : 0 < collisionScale
  illposednessScale_pos : 0 < illposednessScale
  vandermonde_gap_formula :
    localBilipschitz.vandermondeLower = collisionScale * collisionGap
  prefactor_bound :
    collisionScale ≤ illposednessScale * localBilipschitz.operatorNormUpper ^ (κ - 1)

/-- The inverse reconstruction Lipschitz constant is the reciprocal of the positive local
bilipschitz inverse constant. -/
noncomputable def xi_scan_collision_illposedness_inverse_reconstruction_lipschitz {κ : ℕ}
    (D : xi_scan_collision_illposedness_data κ) : ℝ :=
  1 / xi_scan_min_separation_local_bilipschitz_inverse_constant D.localBilipschitz

/-- The collision-scale witness coming from the linearized separation law
`sep ∼ Δ * |γ_j - γ_k|`. -/
noncomputable def xi_scan_collision_illposedness_collision_blowup_witness {κ : ℕ}
    (D : xi_scan_collision_illposedness_data κ) : ℝ :=
  (1 / D.illposednessScale) * (1 / D.collisionGap)

/-- Paper-facing `xi`-scan collision ill-posedness package. The separated scan remains locally
bilipschitz away from collisions, the Hankel block keeps its Vandermonde factorization and full
rank, and the inverse reconstruction Lipschitz constant blows up at least like
`1 / (Δ * |γ_j - γ_k|)` along a two-node collision. -/
def xi_scan_collision_illposedness_holds {κ : ℕ}
    (D : xi_scan_collision_illposedness_data κ) : Prop :=
  xi_scan_min_separation_local_bilipschitz_holds D.localBilipschitz ∧
    D.atomicMoment.hankelDetFactorsAsVandermondeSquare ∧
    D.atomicMoment.hankel.rank = κ ∧
    0 < xi_scan_collision_illposedness_inverse_reconstruction_lipschitz D ∧
    xi_scan_collision_illposedness_collision_blowup_witness D ≤
      xi_scan_collision_illposedness_inverse_reconstruction_lipschitz D

/-- Paper label: `cor:xi-scan-collision-illposedness`. The separated finite-defect reconstruction
package supplies the positive local inverse constant, the Hankel determinant formula keeps the
moment block nondegenerate, and the collision asymptotic `sep ∼ Δ * |γ_j - γ_k|` turns the
reciprocal local inverse constant into an explicit `1 / |γ_j - γ_k|` blow-up witness. -/
theorem paper_xi_scan_collision_illposedness (κ : ℕ)
    (D : xi_scan_collision_illposedness_data κ) : xi_scan_collision_illposedness_holds D := by
  have hbilip := paper_xi_scan_min_separation_local_bilipschitz κ D.localBilipschitz
  have hhankel :=
    paper_xi_comoving_scan_hankel_rank_defect κ D.atomicMoment D.weights_nonzero D.nodes_injective
  have hinv_const_pos :
      0 < xi_scan_min_separation_local_bilipschitz_inverse_constant D.localBilipschitz :=
    hbilip.2.2.2.1
  have hinv_pos : 0 < xi_scan_collision_illposedness_inverse_reconstruction_lipschitz D := by
    dsimp [xi_scan_collision_illposedness_inverse_reconstruction_lipschitz]
    exact one_div_pos.mpr hinv_const_pos
  have hopow_pos : 0 < D.localBilipschitz.operatorNormUpper ^ (κ - 1) := by
    exact pow_pos D.localBilipschitz.operatorNormUpper_pos _
  have hinv_le :
      xi_scan_min_separation_local_bilipschitz_inverse_constant D.localBilipschitz ≤
        D.illposednessScale * D.collisionGap := by
    dsimp [xi_scan_min_separation_local_bilipschitz_inverse_constant]
    rw [D.vandermonde_gap_formula]
    have hmul :=
      mul_le_mul_of_nonneg_right D.prefactor_bound (le_of_lt D.collisionGap_pos)
    exact (_root_.div_le_iff₀ hopow_pos).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  have hblowup :
      xi_scan_collision_illposedness_collision_blowup_witness D ≤
        xi_scan_collision_illposedness_inverse_reconstruction_lipschitz D := by
    have hscalegap_pos : 0 < D.illposednessScale * D.collisionGap := by
      exact mul_pos D.illposednessScale_pos D.collisionGap_pos
    have hone :
        1 / (D.illposednessScale * D.collisionGap) ≤
          1 / xi_scan_min_separation_local_bilipschitz_inverse_constant D.localBilipschitz := by
      exact one_div_le_one_div_of_le hinv_const_pos hinv_le
    have hrewrite :
        xi_scan_collision_illposedness_collision_blowup_witness D =
          1 / (D.illposednessScale * D.collisionGap) := by
      unfold xi_scan_collision_illposedness_collision_blowup_witness
      field_simp [D.illposednessScale_pos.ne', D.collisionGap_pos.ne']
    simpa [xi_scan_collision_illposedness_inverse_reconstruction_lipschitz, hrewrite] using hone
  exact ⟨hbilip, hhankel.1, hhankel.2, hinv_pos, hblowup⟩

end Omega.Zeta
