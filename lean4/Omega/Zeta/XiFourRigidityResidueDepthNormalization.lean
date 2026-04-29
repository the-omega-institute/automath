import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTwoBaseResidueRatioUniqueRecovery

namespace Omega.Zeta

open scoped BigOperators
open TwoBaseResidueRatioRecoveryData

noncomputable def xi_four_rigidity_residue_depth_normalization_single_atom_residue
    (c depth : ℕ) : ℂ :=
  (c : ℂ) * residueRatio 1 (depth : ℂ)

noncomputable def xi_four_rigidity_residue_depth_normalization_profile_residue
    (c : ℕ) (profile : Finset ℕ) : ℂ :=
  profile.sum fun depth =>
    xi_four_rigidity_residue_depth_normalization_single_atom_residue c depth

noncomputable def xi_four_rigidity_residue_depth_normalization_geometric_depth_weight
    (profile : Finset ℕ) : ℂ :=
  profile.sum fun depth =>
    xi_four_rigidity_residue_depth_normalization_single_atom_residue 4 depth

def xi_four_rigidity_residue_depth_normalization_statement : Prop :=
  xi_four_rigidity_residue_depth_normalization_profile_residue 4 ({1} : Finset ℕ) =
      xi_four_rigidity_residue_depth_normalization_geometric_depth_weight ({1} : Finset ℕ) ∧
    ∀ c : ℕ,
      xi_four_rigidity_residue_depth_normalization_profile_residue c ({1} : Finset ℕ) =
          xi_four_rigidity_residue_depth_normalization_geometric_depth_weight ({1} : Finset ℕ) →
        c = 4

/-- Paper label: `prop:xi-four-rigidity-residue-depth-normalization`.
The base-`1` residue-ratio normalization reduces each single-atom residue contribution to the
coefficient itself, finite profiles sum linearly, and matching the geometric depth weight on the
singleton profile forces the normalization constant to be `4`. -/
theorem paper_xi_four_rigidity_residue_depth_normalization :
    xi_four_rigidity_residue_depth_normalization_statement := by
  constructor
  · simp [xi_four_rigidity_residue_depth_normalization_profile_residue,
      xi_four_rigidity_residue_depth_normalization_geometric_depth_weight,
      xi_four_rigidity_residue_depth_normalization_single_atom_residue,
      TwoBaseResidueRatioRecoveryData.residueRatio]
  · intro c hc
    have hc' : (c : ℂ) = 4 := by
      simpa [xi_four_rigidity_residue_depth_normalization_statement,
        xi_four_rigidity_residue_depth_normalization_profile_residue,
        xi_four_rigidity_residue_depth_normalization_geometric_depth_weight,
        xi_four_rigidity_residue_depth_normalization_single_atom_residue,
        TwoBaseResidueRatioRecoveryData.residueRatio] using hc
    exact_mod_cast hc'

end Omega.Zeta
