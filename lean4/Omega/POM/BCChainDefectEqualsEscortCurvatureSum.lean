import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.POM.BeckChevalleyAmgmDefectIdentity

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- Concrete finite chain of two-fiber BC stages. -/
structure pom_bc_chain_defect_equals_escort_curvature_sum_data where
  pom_bc_chain_defect_equals_escort_curvature_sum_depth : ℕ
  pom_bc_chain_defect_equals_escort_curvature_sum_left :
    Fin pom_bc_chain_defect_equals_escort_curvature_sum_depth → ℕ
  pom_bc_chain_defect_equals_escort_curvature_sum_right :
    Fin pom_bc_chain_defect_equals_escort_curvature_sum_depth → ℕ
  pom_bc_chain_defect_equals_escort_curvature_sum_left_pos :
    ∀ i, 0 < pom_bc_chain_defect_equals_escort_curvature_sum_left i
  pom_bc_chain_defect_equals_escort_curvature_sum_right_pos :
    ∀ i, 0 < pom_bc_chain_defect_equals_escort_curvature_sum_right i

namespace pom_bc_chain_defect_equals_escort_curvature_sum_data

/-- The stagewise Beck-Chevalley defect. -/
def pom_bc_chain_defect_equals_escort_curvature_sum_stage_kl_defect
    (D : pom_bc_chain_defect_equals_escort_curvature_sum_data)
    (i : Fin D.pom_bc_chain_defect_equals_escort_curvature_sum_depth) : ℝ :=
  twoFiberAmgmDefect
    (D.pom_bc_chain_defect_equals_escort_curvature_sum_left i)
    (D.pom_bc_chain_defect_equals_escort_curvature_sum_right i)

/-- The stagewise escort-curvature remainder. -/
def pom_bc_chain_defect_equals_escort_curvature_sum_stage_escort_curvature
    (D : pom_bc_chain_defect_equals_escort_curvature_sum_data)
    (i : Fin D.pom_bc_chain_defect_equals_escort_curvature_sum_depth) : ℝ :=
  pom_bc_amgm_defect_escort_variance_energy_potential
      (D.pom_bc_chain_defect_equals_escort_curvature_sum_left i)
      (D.pom_bc_chain_defect_equals_escort_curvature_sum_right i) 1 -
    pom_bc_amgm_defect_escort_variance_energy_mean
      (D.pom_bc_chain_defect_equals_escort_curvature_sum_left i)
      (D.pom_bc_chain_defect_equals_escort_curvature_sum_right i) 0

/-- The chain KL defect is the sum of the local BC defects. -/
def pom_bc_chain_defect_equals_escort_curvature_sum_chain_kl_defect
    (D : pom_bc_chain_defect_equals_escort_curvature_sum_data) : ℝ :=
  ∑ i, D.pom_bc_chain_defect_equals_escort_curvature_sum_stage_kl_defect i

/-- The escort-curvature total is the sum of the local escort remainders. -/
def pom_bc_chain_defect_equals_escort_curvature_sum_escort_curvature_sum
    (D : pom_bc_chain_defect_equals_escort_curvature_sum_data) : ℝ :=
  ∑ i, D.pom_bc_chain_defect_equals_escort_curvature_sum_stage_escort_curvature i

lemma pom_bc_chain_defect_equals_escort_curvature_sum_stage_eq
    (D : pom_bc_chain_defect_equals_escort_curvature_sum_data)
    (i : Fin D.pom_bc_chain_defect_equals_escort_curvature_sum_depth) :
    D.pom_bc_chain_defect_equals_escort_curvature_sum_stage_kl_defect i =
      D.pom_bc_chain_defect_equals_escort_curvature_sum_stage_escort_curvature i := by
  unfold pom_bc_chain_defect_equals_escort_curvature_sum_stage_kl_defect
    pom_bc_chain_defect_equals_escort_curvature_sum_stage_escort_curvature
  symm
  exact
    (paper_pom_bc_amgm_defect_escort_variance_energy
      (D.pom_bc_chain_defect_equals_escort_curvature_sum_left i)
      (D.pom_bc_chain_defect_equals_escort_curvature_sum_right i)
      (D.pom_bc_chain_defect_equals_escort_curvature_sum_left_pos i)
      (D.pom_bc_chain_defect_equals_escort_curvature_sum_right_pos i)).2.2.2

end pom_bc_chain_defect_equals_escort_curvature_sum_data

open pom_bc_chain_defect_equals_escort_curvature_sum_data

/-- Paper label: `thm:pom-bc-chain-defect-equals-escort-curvature-sum`. Summing the local
two-fiber escort-curvature identity along the chain identifies the full BC defect with the full
escort-curvature sum. -/
theorem paper_pom_bc_chain_defect_equals_escort_curvature_sum
    (D : pom_bc_chain_defect_equals_escort_curvature_sum_data) :
    D.pom_bc_chain_defect_equals_escort_curvature_sum_chain_kl_defect =
      D.pom_bc_chain_defect_equals_escort_curvature_sum_escort_curvature_sum := by
  unfold pom_bc_chain_defect_equals_escort_curvature_sum_chain_kl_defect
    pom_bc_chain_defect_equals_escort_curvature_sum_escort_curvature_sum
  exact Finset.sum_congr rfl (fun i _ => D.pom_bc_chain_defect_equals_escort_curvature_sum_stage_eq i)

end

end Omega.POM
