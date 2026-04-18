import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local strip-kernel wrapper for the sharp point-evaluation statement. The data records
an abstract RKHS carrier together with its strip evaluations, the diagonal-kernel size on the
strip, the restriction isometry, and the kernel-section witness that saturates the standard RKHS
point-evaluation bound. -/
structure KernelStripExtensionEvalData where
  Carrier : Type
  norm : Carrier → ℝ
  realAxisNorm : Carrier → ℝ
  evalAt : ℝ → ℝ → Carrier → ℂ
  stripDiagonal : ℝ → ℝ
  restrictionIsometryWitness : ∀ f : Carrier, realAxisNorm f = norm f
  stripDiagonal_pos : ∀ y : ℝ, -1 < y → y < 1 → 0 < stripDiagonal y
  stripDiagonal_sqrt :
    ∀ y : ℝ, -1 < y → y < 1 →
      Real.sqrt (stripDiagonal y) = 1 / Real.sqrt (2 * (1 - y ^ 2))
  eval_bound :
    ∀ x y : ℝ, -1 < y → y < 1 → ∀ f : Carrier,
      ‖evalAt x y f‖ ≤ Real.sqrt (stripDiagonal y) * norm f
  sharpness :
    ∀ x y : ℝ, -1 < y → y < 1 →
      ∃ f : Carrier, norm f = 1 ∧ ‖evalAt x y f‖ = Real.sqrt (stripDiagonal y)

/-- Positivity of the strip kernel, read off from the diagonal section norm. -/
def KernelStripExtensionEvalData.stripKernelPositive (D : KernelStripExtensionEvalData) : Prop :=
  ∀ y : ℝ, -1 < y → y < 1 → 0 < D.stripDiagonal y

/-- The restriction map from the strip space to the real-axis RKHS is an isometry. -/
def KernelStripExtensionEvalData.restrictionIsometry (D : KernelStripExtensionEvalData) : Prop :=
  ∀ f : D.Carrier, D.realAxisNorm f = D.norm f

/-- Sharp point-evaluation on the strip: for each horizontal slice `y ∈ (-1,1)` and every real
abscissa `x`, the RKHS evaluation functional has norm `1 / √(2 (1 - y²))`, and that constant is
attained by a kernel section. -/
def KernelStripExtensionEvalData.sharpPointEval
    (D : KernelStripExtensionEvalData) (y : ℝ) : Prop :=
  ∀ x : ℝ,
    (∀ f : D.Carrier,
      ‖D.evalAt x y f‖ ≤ 1 / Real.sqrt (2 * (1 - y ^ 2)) * D.norm f) ∧
    ∃ f : D.Carrier, D.norm f = 1 ∧
      ‖D.evalAt x y f‖ = 1 / Real.sqrt (2 * (1 - y ^ 2))

/-- Paper-facing strip-extension wrapper: the strip kernel stays positive, restriction to the real
axis is isometric, and the diagonal kernel value gives the sharp point-evaluation constant.
    prop:cdim-kernel-strip-extension-eval -/
theorem paper_cdim_kernel_strip_extension_eval (D : KernelStripExtensionEvalData) :
    D.stripKernelPositive ∧ D.restrictionIsometry ∧
      (forall y : Real, -1 < y -> y < 1 -> D.sharpPointEval y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy_low hy_high
    exact D.stripDiagonal_pos y hy_low hy_high
  · exact D.restrictionIsometryWitness
  · intro y hy_low hy_high x
    refine ⟨?_, ?_⟩
    · intro f
      simpa [D.stripDiagonal_sqrt y hy_low hy_high] using D.eval_bound x y hy_low hy_high f
    · rcases D.sharpness x y hy_low hy_high with ⟨f, hnorm, hsharp⟩
      refine ⟨f, hnorm, ?_⟩
      simpa [D.stripDiagonal_sqrt y hy_low hy_high] using hsharp

end Omega.CircleDimension
