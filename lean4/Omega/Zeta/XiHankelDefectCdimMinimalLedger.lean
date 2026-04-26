import Mathlib.Tactic
import Omega.CircleDimension.XiCdimMinimalLedgerCost

namespace Omega.Zeta

structure xi_hankel_defect_cdim_minimal_ledger_data where
  ambientRank : ℕ
  rationalRank : ℕ
  rationalRank_le : rationalRank ≤ ambientRank

namespace xi_hankel_defect_cdim_minimal_ledger_data

def xi_hankel_defect_cdim_minimal_ledger_defect
    (D : xi_hankel_defect_cdim_minimal_ledger_data) : ℕ :=
  D.ambientRank - D.rationalRank

def xi_hankel_defect_cdim_minimal_ledger_homData
    (D : xi_hankel_defect_cdim_minimal_ledger_data) : Omega.CircleDimension.CircleDimHomData where
  sourceRank := D.ambientRank
  targetRank := D.ambientRank
  kernelRank := D.xi_hankel_defect_cdim_minimal_ledger_defect
  imageRank := D.rationalRank
  rankNullity := by
    unfold xi_hankel_defect_cdim_minimal_ledger_defect
    exact (Nat.sub_add_cancel D.rationalRank_le).symm
  imageBound := D.rationalRank_le

def xi_hankel_defect_cdim_minimal_ledger_circleKernel
    (D : xi_hankel_defect_cdim_minimal_ledger_data) : ℕ :=
  Omega.CircleDimension.circleDim D.xi_hankel_defect_cdim_minimal_ledger_defect 0

def xi_hankel_defect_cdim_minimal_ledger_spec
    (D : xi_hankel_defect_cdim_minimal_ledger_data) : Prop :=
  D.xi_hankel_defect_cdim_minimal_ledger_circleKernel =
      D.xi_hankel_defect_cdim_minimal_ledger_defect ∧
    (∀ R_rank : ℕ,
      D.xi_hankel_defect_cdim_minimal_ledger_defect ≤ R_rank →
        D.xi_hankel_defect_cdim_minimal_ledger_circleKernel ≤
          Omega.CircleDimension.circleDim R_rank 0) ∧
    (∀ R_rank : ℕ,
      D.xi_hankel_defect_cdim_minimal_ledger_circleKernel ≤
          Omega.CircleDimension.circleDim R_rank 0 ↔
        D.xi_hankel_defect_cdim_minimal_ledger_defect ≤ R_rank) ∧
    ∃ R_rank : ℕ,
      D.xi_hankel_defect_cdim_minimal_ledger_circleKernel =
        Omega.CircleDimension.circleDim R_rank 0

end xi_hankel_defect_cdim_minimal_ledger_data

open xi_hankel_defect_cdim_minimal_ledger_data

theorem paper_xi_hankel_defect_cdim_minimal_ledger
    (D : xi_hankel_defect_cdim_minimal_ledger_data) :
    xi_hankel_defect_cdim_minimal_ledger_spec D := by
  have hkernel :
      D.xi_hankel_defect_cdim_minimal_ledger_homData.kernelRank =
        D.xi_hankel_defect_cdim_minimal_ledger_defect := rfl
  rcases Omega.CircleDimension.paper_xi_cdim_minimal_ledger_cost
      D.xi_hankel_defect_cdim_minimal_ledger_homData with
    ⟨hlower, hattained⟩
  refine ⟨by simp [xi_hankel_defect_cdim_minimal_ledger_circleKernel, Omega.CircleDimension.circleDim],
    ?_, ?_, ?_⟩
  · intro R_rank hR
    simpa [xi_hankel_defect_cdim_minimal_ledger_circleKernel, hkernel] using hlower R_rank hR
  · intro R_rank
    simp [xi_hankel_defect_cdim_minimal_ledger_circleKernel, Omega.CircleDimension.circleDim]
  · rcases hattained with ⟨R_rank, hR⟩
    exact ⟨R_rank, by simpa [xi_hankel_defect_cdim_minimal_ledger_circleKernel, hkernel] using
      hR.symm⟩

end Omega.Zeta
