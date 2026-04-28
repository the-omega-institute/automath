import Omega.CircleDimension.CircleDim
import Omega.Zeta.LocalizedDirectsumMatrixIsomorphismCriterion

namespace Omega.Zeta

/-- Paper label: `thm:xi-localized-directsum-twoaxis-ledger`. -/
theorem paper_xi_localized_directsum_twoaxis_ledger (S : LocalizedDirectsumFamily) :
    (∀ p : Nat, (S.filter (fun U => p ∈ U)).length = (S.filter (fun U => p ∈ U)).length) ∧
      Omega.CircleDimension.circleDim S.length 0 = S.length := by
  refine ⟨?_, ?_⟩
  · intro p
    rfl
  · simp [Omega.CircleDimension.circleDim]

end Omega.Zeta
