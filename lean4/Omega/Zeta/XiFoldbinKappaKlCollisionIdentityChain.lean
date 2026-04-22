import Mathlib.Tactic
import Omega.Folding.FoldBinChi2Col
import Omega.Folding.FoldBinEscortEscortKl

namespace Omega.Zeta

open Omega.Folding

/-- Same-temperature escort `κ` term. -/
noncomputable def xiFoldbinKappa (q : ℝ) : ℝ :=
  killoEscortKLDivergence q q

/-- Paper label: `thm:xi-foldbin-kappa-kl-collision-identity-chain`.
At equal escort temperatures the Bernoulli KL term collapses to `κ = 0`; this gives the lower
bound by KL nonnegativity, the collision expression is nonnegative by construction, and the
bin-fold `χ²` identity rewrites it as `χ² + 1`. -/
theorem paper_xi_foldbin_kappa_kl_collision_identity_chain (q : ℝ) (hq : 0 ≤ q) (m : ℕ) :
    let D : FoldBinEscortEscortKlData := { p := q, q := q, hp := hq, hq := hq }
    xiFoldbinKappa q = D.klLimit ∧
      0 ≤ xiFoldbinKappa q ∧
      xiFoldbinKappa q ≤
        (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ) ∧
      (((Omega.Folding.foldBinChi2Col m : ℚ) : ℝ) + 1 =
        (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ)) := by
  dsimp
  have hkl :
      xiFoldbinKappa q =
        ({ p := q, q := q, hp := hq, hq := hq } : FoldBinEscortEscortKlData).klLimit := by
    simpa [xiFoldbinKappa] using
      (paper_fold_bin_escort_escort_kl
        ({ p := q, q := q, hp := hq, hq := hq } : FoldBinEscortEscortKlData)).symm
  have htheta_ne : killoEscortTheta q ≠ 0 := (killoEscortTheta_pos q).ne'
  have hone_sub_ne : 1 - killoEscortTheta q ≠ 0 := by
    have hlt : killoEscortTheta q < 1 := killoEscortTheta_lt_one q
    linarith
  have hkappa_zero : xiFoldbinKappa q = 0 := by
    unfold xiFoldbinKappa killoEscortKLDivergence
    rw [div_self htheta_ne, div_self hone_sub_ne]
    simp
  have hcollision_nonneg : 0 ≤ Omega.Folding.foldBinCollisionMass m := by
    unfold Omega.Folding.foldBinCollisionMass
    exact Finset.sum_nonneg fun x _hx => sq_nonneg (Omega.Folding.foldBinMass m x)
  have hbound_nonneg :
      0 ≤ (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ) := by
    exact mul_nonneg (by positivity) (by exact_mod_cast hcollision_nonneg)
  have hchi :
      (((Omega.Folding.foldBinChi2Col m : ℚ) : ℝ) + 1 =
        (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ)) := by
    have hchiQ := paper_fold_bin_chi2_col m
    have hchiR :
        ((Omega.Folding.foldBinChi2Col m : ℚ) : ℝ) =
          (Fintype.card (Omega.X m) : ℝ) * (Omega.Folding.foldBinCollisionMass m : ℚ) - 1 := by
      exact_mod_cast hchiQ
    linarith
  refine ⟨hkl, ?_, ?_, hchi⟩
  · rw [hkappa_zero]
  · rw [hkappa_zero]
    exact hbound_nonneg

end Omega.Zeta
