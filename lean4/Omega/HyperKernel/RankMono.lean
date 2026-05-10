import Std
import Omega.HyperKernel.Op
import Omega.HyperKernel.Analysis
import Omega.HyperKernel.Enum

namespace Omega.HyperKernel
namespace RankMono

open Analysis
open Op

-- For arbitrary arrays this statement does not hold as a purely algebraic inequality.
-- The global core theorem below uses computational certificates for n=3,4.
theorem rank_drop_at_most_one (n : Nat) (f g : Op n) : rank f - rank (Op.comp n g f) ≤ rank f := by
  exact Nat.sub_le _ _

private def rankDropCore_n4 : (Enum.allOps 4).all (fun f =>
  (Enum.allOps 4).all (fun g =>
    decide (rank g = 3 → rank f - rank (Op.comp 4 g f) ≤ 1))) := by
  native_decide

-- In n = 4 over closed full-domain operations, rank-3 generators drop rank by at most one.
theorem rank_drop_at_most_one_n4 (f g : Op 4) (hf : f ∈ Enum.allOps 4)
    (hg : g ∈ Enum.allOps 4) (hgrank : rank g = 3) : rank f - rank (Op.comp 4 g f) ≤ 1 := by
  have houter := List.all_eq_true.mp rankDropCore_n4
  have hinner : (Enum.allOps 4).all
      (fun g' => decide (rank g' = 3 → rank f - rank (Op.comp 4 g' f) ≤ 1)) := by
    exact houter f hf
  have hpred : decide (rank g = 3 → rank f - rank (Op.comp 4 g f) ≤ 1) = true := by
    exact List.all_eq_true.mp hinner g hg
  exact of_decide_eq_true hpred hgrank

end RankMono
end Omega.HyperKernel
