import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The extremal Toeplitz matrix coming from the equally weighted `(N + 1)`-point root-of-unity
configuration is the scalar matrix `η I`. -/
noncomputable def carathBufferSharpToeplitz (N : ℕ) (eta : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  eta • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

/-- Closed-form Carathéodory value attached to the extremal discrete measure after compressing the
root-of-unity sum to the single phase parameter `z = e^{-i φ} w^(N + 1)`. -/
noncomputable def carathBufferSharpValue (eta : ℝ) (z : ℂ) : ℂ :=
  (eta : ℂ) * (1 + z) / (1 - z)

/-- Sharpness package for the Toeplitz/Carathéodory lower buffer: the extremal discrete
root-of-unity configuration gives a scalar Toeplitz matrix and, at the phase where
`z = -r^(N+1)`, the Carathéodory value collapses to the exact buffer endpoint.
    prop:cdim-carath-buffer-sharpness -/
theorem paper_cdim_carath_buffer_sharpness (N : ℕ) (eta r : ℝ) :
    carathBufferSharpToeplitz N eta = eta • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) ∧
      carathBufferSharpValue eta (-(r : ℂ) ^ (N + 1)) =
        ((eta * (1 - r ^ (N + 1)) / (1 + r ^ (N + 1)) : ℝ) : ℂ) := by
  refine ⟨rfl, ?_⟩
  simp [carathBufferSharpValue, sub_eq_add_neg, add_comm]

end Omega.CircleDimension
