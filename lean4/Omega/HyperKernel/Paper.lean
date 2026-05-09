import Omega.HyperKernel.SetStructure
import Omega.HyperKernel.Fiber
import Omega.HyperKernel.Geometry
import Omega.HyperKernel.SetStructureChecksTiny

namespace Omega.HyperKernel.Paper

open SetStructure

/-- The finite HyperKernel carrier realizes points as rank-one idempotents.
    app:hyperkernel-finite-certificate -/
def PointObject (n : Nat) := SetStructure.Point n

/-- The finite HyperKernel carrier realizes set objects as idempotent projections.
    app:hyperkernel-finite-certificate -/
def SetObject (n : Nat) := SetStructure.SetObj n

/-- Membership in the HyperKernel finite carrier is stability under projection.
    app:hyperkernel-finite-certificate -/
theorem paper_hyperkernel_membership_is_stability
    (n : Nat) (p : PointObject n) (s : SetObject n) :
    SetStructure.belongs n p s ↔ Op.comp n s.1 p.1 = p.1 := by
  rfl

/-- Rank-one idempotents are counted correctly in the `n = 4` finite carrier.
    app:hyperkernel-finite-certificate -/
theorem paper_hyperkernel_point_count_n4 :
    (SetStructure.pointObjects 4).length = 4 :=
  Omega.HyperKernel.SetStructureChecksTiny.pointCount_n4

/-- Signature budgets provide the finite action filtration used by the appendix.
    app:hyperkernel-finite-certificate -/
def paper_hyperkernel_signature_budget_curve
    (n : Nat) (dict : Closure.Dict n) (maxLen : Nat) : List (Nat × Nat) :=
  SetStructure.signatureCountCurve n dict maxLen

/-- Rank fibers provide the finite geometric stratification used by the appendix.
    app:hyperkernel-finite-certificate -/
def paper_hyperkernel_rank_fibers
    (n : Nat) (dict : Closure.Dict n) : List (Nat × List (Op n)) :=
  Fiber.foldByRank n dict

/-- Generator-square residuals provide the finite curvature readout used by the appendix.
    app:hyperkernel-finite-certificate -/
def paper_hyperkernel_square_curvature
    (n : Nat) (gens : List (Op n)) (dict : Closure.Dict n)
    (op : Op n) (i j : Nat) : Option Int :=
  Geometry.squareCurvatureAt n gens dict op i j

end Omega.HyperKernel.Paper
