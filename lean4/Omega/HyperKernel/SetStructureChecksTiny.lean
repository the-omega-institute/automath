import Omega.HyperKernel.SetStructure
import Omega.HyperKernel.Enum
import Omega.HyperKernel.AutoSeed

namespace Omega.HyperKernel.SetStructureChecksTiny

theorem pointCount_n4 : (Omega.HyperKernel.SetStructure.pointObjects 4).length = 4 := by
  native_decide

end Omega.HyperKernel.SetStructureChecksTiny
