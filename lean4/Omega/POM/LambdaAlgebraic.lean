import Mathlib

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for algebraic realization of the partition constants in
    `2026_projection_ontological_mathematics_core_tams`.
    cor:lambda-algebraic -/
theorem paper_projection_lambda_algebraic
    {R Matrix CMatrix : Type}
    (lam : ℕ → R)
    (ρ : Matrix → R)
    (ρc : CMatrix → R)
    (dim polyBound : ℕ → ℕ)
    (A : ℕ → Matrix)
    (Atilde : ℕ → CMatrix)
    (algInt : R → Prop)
    {q : ℕ}
    (_hq : 2 ≤ q)
    (hRealize : ρ (A q) = lam q)
    (hCompress : ρc (Atilde q) = lam q)
    (hDim : dim q ≤ polyBound q)
    (hAlg : algInt (ρc (Atilde q))) :
    (lam q = ρ (A q)) ∧
      (lam q = ρc (Atilde q)) ∧
      dim q ≤ polyBound q ∧
      algInt (lam q) := by
  refine ⟨hRealize.symm, hCompress.symm, hDim, ?_⟩
  simpa [hCompress] using hAlg

end Omega.POM
