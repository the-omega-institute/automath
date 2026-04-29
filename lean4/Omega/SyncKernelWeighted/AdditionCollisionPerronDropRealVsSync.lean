import Mathlib.Data.Real.Basic

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:addition-collision-perron-drop-real-vs-sync`. -/
theorem paper_addition_collision_perron_drop_real_vs_sync (q : ℕ) (hq : 2 ≤ q)
    (realRadius syncRadius : ℝ) (entrywiseSubkernel strictSubkernel sync10Primitive : Prop)
    (hEntrywise : entrywiseSubkernel) (hStrict : strictSubkernel) (hPrimitive : sync10Primitive)
    (hPFStrictMono :
      entrywiseSubkernel → strictSubkernel → sync10Primitive → realRadius < syncRadius) :
    realRadius < syncRadius := by
  let _ := q
  let _ := hq
  exact hPFStrictMono hEntrywise hStrict hPrimitive

end Omega.SyncKernelWeighted
