import Omega.HyperKernel.SetStructure
import Omega.HyperKernel.Enum
import Omega.HyperKernel.AutoSeed

namespace Omega.HyperKernel
namespace SetStructureChecksLite

open SetStructure
open Closure
open AutoSeed

/-- rank-1 idempotents for n=3 and n=4 -/
theorem pointCount_n3 : (pointObjects 3).length = 3 := by
  native_decide

theorem pointCount_n4 : (pointObjects 4).length = 4 := by
  native_decide

/-- idempotents for n=3 and n=4 -/
theorem setObjCount_n3 : (setObjects 3).length = 10 := by
  native_decide

theorem setObjCount_n4 : (setObjects 4).length = 41 := by
  native_decide

/-- canonical signature curve from seed generators -/
def seedClosure_n4 : Option (Closure.Dict 4) := do
  match AutoSeed.findMinGenerators 4 3 with
  | some (_, gens) =>
      pure (Closure.closureDict 4 gens (Enum.allOps 4).length)
  | none =>
      none

def signatureCurve_seed_n4 : Option (List (Prod Nat Nat)) :=
  seedClosure_n4 >>= fun dict => some (Omega.HyperKernel.SetStructure.signatureCountCurve 4 dict 7)

/-- every length has a prefix count entry -/
theorem signatureCurve_seed_n4_has8 :
    (signatureCurve_seed_n4).map List.length = some 8 := by
  native_decide

end SetStructureChecksLite
end Omega.HyperKernel
