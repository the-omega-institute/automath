import Omega.EA.SyncKernelMealyMinimality

namespace Omega.SyncKernelWeighted

/-- The visible four input contexts `(p_x, p_y) ∈ {0,1}²` from the real-input-40 product
construction. -/
abbrev RealInput40InputContext := Bool × Bool

/-- The explicit product state space `Q × {0,1}²` used by the appendix construction. -/
abbrev RealInput40ProductState := Omega.EA.SyncKernelState × RealInput40InputContext

/-- The number of explicit input-context states. -/
def realInput40InputContextStateCount : ℕ :=
  Fintype.card RealInput40InputContext

/-- The number of residual normalization states supplied by the synchronizing kernel. -/
def realInput40NormalizationResidualStateCount : ℕ :=
  Fintype.card Omega.EA.SyncKernelState

/-- The number of states in the explicit product construction. -/
def realInput40ProductStateCount : ℕ :=
  Fintype.card RealInput40ProductState

/-- The one-step explicit-input model must keep all four input contexts visible. -/
def realInput40InputContextLowerBound : Prop :=
  4 ≤ realInput40InputContextStateCount

/-- The synchronizing-kernel residual layer contributes at least ten states. -/
def realInput40NormalizationResidualLowerBound : Prop :=
  10 ≤ realInput40NormalizationResidualStateCount

/-- Combining the two independent pieces forces at least forty product states. -/
def realInput40ProductLowerBound : Prop :=
  40 ≤ realInput40ProductStateCount

/-- The explicit appendix construction is sharp: the product state space has exactly forty
states. -/
def realInput40Sharpness : Prop :=
  realInput40ProductStateCount = 40

/-- Paper-facing lower-bound package for the real-input-40 appendix construction: the explicit
input contexts contribute four states, the synchronizing-kernel residuals contribute ten states,
their direct product contributes forty states, and the concrete product construction is sharp.
    thm:real-input-40-product-lower-bound -/
theorem paper_real_input_40_product_lower_bound :
    realInput40InputContextLowerBound ∧
      realInput40NormalizationResidualLowerBound ∧
      realInput40ProductLowerBound ∧
      realInput40Sharpness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 4 ≤ Fintype.card RealInput40InputContext
    native_decide
  · simpa [realInput40NormalizationResidualLowerBound, realInput40NormalizationResidualStateCount]
      using (show 10 ≤ Fintype.card Omega.EA.SyncKernelState by
        simp [Omega.EA.syncKernelState_card])
  · change 40 ≤ Fintype.card RealInput40ProductState
    native_decide
  · change Fintype.card RealInput40ProductState = 40
    native_decide

end Omega.SyncKernelWeighted
