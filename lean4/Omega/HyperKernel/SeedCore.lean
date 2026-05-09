import Omega.HyperKernel.Enum
import Omega.HyperKernel.Analysis
import Omega.HyperKernel.AutoSeed
import Omega.HyperKernel.Closure
import Omega.HyperKernel.RankMono

namespace HyperKernel
namespace SeedCore

open Analysis

-- All 3-ary maps: rank never drops by more than 1 under left composition.
theorem rankDropCore_n3 :
    ((Enum.allOps 3).all (fun f =>
      (Enum.allOps 3).all (fun g =>
        decide (rank g = 2 → rank f ≤ rank (Op.comp 3 g f) + 1))) = true) := by
  native_decide

-- All 3-ary maps: rank never increases under left composition.
theorem rankCompCore_n3 :
    ((Enum.allOps 3).all (fun f =>
      (Enum.allOps 3).all (fun g =>
        decide (rank (Op.comp 3 g f) ≤ rank f))) = true) := by
  native_decide

-- All 4-ary maps: for every defect-1 singular generator, rank drops by at most one.
theorem rankDropCore_n4 :
    ((Enum.allOps 4).all (fun f =>
      (Enum.allOps 4).all (fun g =>
        decide (rank g = 3 → rank f - rank (Op.comp 4 g f) ≤ 1))) = true) := by
  native_decide

-- All 4-ary maps: rank never increases under left composition.
theorem rankCompCore_n4 :
    ((Enum.allOps 4).all (fun f =>
      (Enum.allOps 4).all (fun g =>
        decide (rank (Op.comp 4 g f) ≤ rank f))) = true) := by
  native_decide

-- n = 3 seed search does exist with bounded search depth 3.
theorem autoSeedFound_n3 : (AutoSeed.findMinGenerators 3 3).isSome := by
  native_decide

-- n = 4 seed search does exist with bounded search depth 3.
theorem autoSeedFound_n4 : (AutoSeed.findMinGenerators 4 3).isSome := by
  native_decide

end SeedCore
end HyperKernel
