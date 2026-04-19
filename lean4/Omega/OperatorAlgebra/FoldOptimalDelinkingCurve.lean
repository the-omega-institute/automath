import Mathlib.Tactic

namespace Omega.OperatorAlgebra

noncomputable section

/-- The lower envelope predicted by the strong-duality argument. -/
def foldOptimalDelinkingCurve (Gamma h : Real) : Real :=
  max (Gamma - h) 0

/-- An explicit piecewise family that saturates the lower envelope. -/
def foldSaturatingDelinkingLeakage (Gamma h : Real) : Real :=
  if h ≤ Gamma then Gamma - h else 0

/-- Scalar-proxy formulation of the optimal delinking curve: any protocol whose leakage and
randomness budget satisfy the chain-rule inequality must lie above the lower envelope, and the
piecewise family realizes that envelope exactly. -/
def FoldOptimalDelinkingCurveStatement (Gamma h : Real) : Prop :=
  (∀ leakage randomness : Real,
      0 ≤ leakage →
      Gamma ≤ leakage + randomness →
      randomness ≤ h →
      foldOptimalDelinkingCurve Gamma h ≤ leakage) ∧
    foldSaturatingDelinkingLeakage Gamma h = foldOptimalDelinkingCurve Gamma h

/-- The chain-rule lower bound gives the optimal delinking curve `max (Gamma - h) 0`, and the
piecewise family `foldSaturatingDelinkingLeakage` attains it exactly.
    thm:op-algebra-optimal-delinking-curve -/
theorem paper_op_algebra_optimal_delinking_curve (Gamma h : Real) (hGamma : 0 <= Gamma) :
    FoldOptimalDelinkingCurveStatement Gamma h := by
  have _ : 0 ≤ Gamma := hGamma
  refine ⟨?_, ?_⟩
  · intro leakage randomness hLeak hChain hBudget
    have hGap : Gamma - h ≤ leakage := by
      linarith
    exact max_le_iff.mpr ⟨hGap, hLeak⟩
  · by_cases hh : h ≤ Gamma
    · simp [foldSaturatingDelinkingLeakage, foldOptimalDelinkingCurve, hh]
    · have hlt : Gamma < h := lt_of_not_ge hh
      have hGap : Gamma - h ≤ 0 := by linarith
      simp [foldSaturatingDelinkingLeakage, foldOptimalDelinkingCurve, hh, max_eq_right hGap]

end

end Omega.OperatorAlgebra
