import Omega.HyperKernel.SetStructure
import Omega.HyperKernel.Enum
import Omega.HyperKernel.AutoSeed

theorem pointCount_n4 : (HyperKernel.SetStructure.pointObjects 4).length = 4 := by
  native_decide
