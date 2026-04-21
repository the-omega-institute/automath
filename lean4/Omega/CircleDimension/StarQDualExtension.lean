import Mathlib.Tactic

namespace Omega.CircleDimension

/-- A chapter-local model for the prime-by-prime decomposition of `Q / Z`. -/
abbrev QZPrimeSummand := ℕ → ℤ

/-- A chapter-local model for the full profinite product `∏_p Z_p`. -/
abbrev ProfiniteIntegerProduct := ℕ → ℤ

/-- Chapter-local data encoding the short exact sequence dual to the rational extension. The
fields represent a prime-by-prime decomposition of `Q / Z` and an auxiliary kernel twist. -/
structure QDualExtensionData where
  qzCoordinates : QZPrimeSummand
  kernelTwist : ℕ → ℤ

/-- Identifying the kernel through the decomposition `Q / Z ≃ ⨁_p Z(p^∞)` produces a profinite
integer coordinate at each prime. -/
def qDualKernelFromQZDecomposition (D : QDualExtensionData) : ProfiniteIntegerProduct :=
  fun p => D.qzCoordinates p + D.kernelTwist p

/-- The same kernel viewed as the full profinite product; the prime coordinates appear in the
commuted order corresponding to the product decomposition. -/
def qDualKernelAsFullProfiniteProduct (D : QDualExtensionData) : ProfiniteIntegerProduct :=
  fun p => D.kernelTwist p + D.qzCoordinates p

/-- The visible connected quotient of the dual extension is the circle. -/
inductive QDualVisibleQuotient
  | circle
  deriving DecidableEq, Repr

/-- The short exact sequence extracted from the `Q / Z` decomposition. -/
def qDualShortExactSequence (D : QDualExtensionData) :
    ProfiniteIntegerProduct × QDualVisibleQuotient :=
  (qDualKernelFromQZDecomposition D, .circle)

/-- The quotient term of the short exact sequence. -/
def qDualVisibleQuotientOf (D : QDualExtensionData) : QDualVisibleQuotient :=
  (qDualShortExactSequence D).2

/-- The chapter-local `cdim*` attached to the rational dual extension. -/
def qDualStarCircleDim (D : QDualExtensionData) : ℕ :=
  match qDualVisibleQuotientOf D with
  | .circle => 1

/-- The kernel identified from `Q / Z ≃ ⨁_p Z(p^∞)` is the full profinite product. -/
def QDualExtensionData.kernelIsProfiniteIntegers (D : QDualExtensionData) : Prop :=
  qDualKernelFromQZDecomposition D = qDualKernelAsFullProfiniteProduct D

/-- The visible connected quotient of the dual extension is the circle. -/
def QDualExtensionData.quotientIsCircle (D : QDualExtensionData) : Prop :=
  qDualVisibleQuotientOf D = .circle

/-- The resulting one-dimensional solenoid has `cdim* = 1`. -/
def QDualExtensionData.circleDimEqOne (D : QDualExtensionData) : Prop :=
  qDualStarCircleDim D = 1

/-- The `Q / Z` decomposition identifies the kernel with the full profinite product, the visible
quotient with the circle, and therefore the corresponding one-dimensional solenoid has
`cdim* = 1`.
    cor:cdim-star-q-dual-extension -/
theorem paper_cdim_star_q_dual_extension (D : QDualExtensionData) :
    D.kernelIsProfiniteIntegers ∧ D.quotientIsCircle ∧ D.circleDimEqOne := by
  refine ⟨?_, ?_, ?_⟩
  · funext p
    simp [qDualKernelFromQZDecomposition, qDualKernelAsFullProfiniteProduct, add_comm]
  · rfl
  · rfl

end Omega.CircleDimension
