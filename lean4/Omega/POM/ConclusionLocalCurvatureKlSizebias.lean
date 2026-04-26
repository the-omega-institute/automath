import Mathlib.Tactic
import Omega.Conclusion.TowerDefectExactTvDuality
import Omega.POM.BeckChevalleyAmgmDefectIdentity
import Omega.POM.LocalDefectGibbsVariational
import Omega.POM.SmallDefectFiberRigidity

namespace Omega.POM

/-- Concrete package for the local-curvature/size-bias conclusion. The one-fiber Gibbs datum
encodes the uniform-to-size-biased KL identity, the tower datum records the exact TV duality, and
the two-fiber endpoint records the Beck-Chevalley escort-energy remainder. -/
structure conclusion_pom_local_curvature_is_kl_sizebias_data where
  gibbs : pom_local_defect_gibbs_variational_data
  tower : Omega.Conclusion.TowerDefectExactTvDualityData
  twoFiberLeft : ℕ
  twoFiberRight : ℕ
  twoFiberLeft_pos : 0 < twoFiberLeft
  twoFiberRight_pos : 0 < twoFiberRight
  pinsker_l1 :
    ∑ i,
        |pom_local_defect_gibbs_variational_uniform_law gibbs.k i -
            pom_local_defect_gibbs_variational_size_biased_law gibbs.fiber_size i| ≤
      Real.sqrt (2 * pom_local_defect_gibbs_variational_defect gibbs.k gibbs.fiber_size)

namespace conclusion_pom_local_curvature_is_kl_sizebias_data

/-- The local curvature is the KL divergence from uniform to the size-biased law, its free-energy
package gives the variational upper bound, the tower defect has exact TV duality, the Pinsker
bound turns into coordinatewise rigidity, and the two-fiber endpoint energy is the escort
remainder. -/
def holds (D : conclusion_pom_local_curvature_is_kl_sizebias_data) : Prop :=
  pom_local_defect_gibbs_variational_defect D.gibbs.k D.gibbs.fiber_size =
      pom_local_defect_gibbs_variational_kl_div
        (pom_local_defect_gibbs_variational_uniform_law D.gibbs.k)
        (pom_local_defect_gibbs_variational_size_biased_law D.gibbs.fiber_size) ∧
    (∀ π : Fin (D.gibbs.k + 1) → ℝ,
      pom_local_defect_gibbs_variational_simplex D.gibbs.k π →
        pom_local_defect_gibbs_variational_free_energy D.gibbs.k D.gibbs.fiber_size π ≤
          pom_local_defect_gibbs_variational_defect D.gibbs.k D.gibbs.fiber_size) ∧
    D.tower.exactTvDuality ∧
    (∀ i : Fin (D.gibbs.k + 1),
      |(D.gibbs.fiber_size i : ℝ) /
          pom_small_defect_fiber_rigidity_arithmetic_mean D.gibbs.fiber_size - 1| ≤
        (D.gibbs.k + 1 : ℝ) *
          Real.sqrt (2 * pom_local_defect_gibbs_variational_defect D.gibbs.k D.gibbs.fiber_size)) ∧
    pom_bc_amgm_defect_escort_variance_energy_potential D.twoFiberLeft D.twoFiberRight 1 -
        pom_bc_amgm_defect_escort_variance_energy_mean D.twoFiberLeft D.twoFiberRight 0 =
      twoFiberAmgmDefect D.twoFiberLeft D.twoFiberRight

end conclusion_pom_local_curvature_is_kl_sizebias_data

open conclusion_pom_local_curvature_is_kl_sizebias_data

/-- Paper label: `thm:conclusion-pom-local-curvature-is-kl-sizebias`. The audited local Gibbs
variational principle identifies the local curvature with the KL divergence from the uniform law to
the size-biased law, the tower-defect duality gives the exact TV observable, Pinsker turns the
same KL quantity into fiber-rigidity bounds, and the Beck-Chevalley escort package records the
matching endpoint energy identity. -/
theorem paper_conclusion_pom_local_curvature_is_kl_sizebias
    (D : conclusion_pom_local_curvature_is_kl_sizebias_data) : D.holds := by
  have hgibbs := paper_pom_local_defect_gibbs_variational D.gibbs
  have htower := Omega.Conclusion.paper_conclusion_pom_tower_defect_exact_tv_duality D.tower
  have hpinsker :
      ∑ i,
          |pom_local_defect_gibbs_variational_uniform_law D.gibbs.k i -
              pom_local_defect_gibbs_variational_size_biased_law D.gibbs.fiber_size i| ≤
        Real.sqrt
          (2 *
            pom_local_defect_gibbs_variational_kl_div
              (pom_local_defect_gibbs_variational_uniform_law D.gibbs.k)
              (pom_local_defect_gibbs_variational_size_biased_law D.gibbs.fiber_size)) := by
    simpa [hgibbs.2.1.symm] using D.pinsker_l1
  have hrigidity := paper_pom_small_defect_fiber_rigidity D.gibbs hpinsker
  have hescort :=
    paper_pom_bc_amgm_defect_escort_variance_energy D.twoFiberLeft D.twoFiberRight
      D.twoFiberLeft_pos D.twoFiberRight_pos
  exact ⟨hgibbs.2.1, hgibbs.2.2.1, htower, hrigidity, hescort.2.2.2⟩

end Omega.POM
