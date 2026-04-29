import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Omega.Zeta.XiHellingerKernelFourierSech2

namespace Omega.Zeta

/-- The chapter-local RKHS surrogate kernel obtained directly from the Hellinger Fourier density.
-/
noncomputable def xi_hellinger_kernel_rkhs_volume_kernel (x y : ℝ) : ℝ :=
  xiHellingerKernelFourierDensity (x - y)

/-- The kernel section anchored at the sampled depth `s j`. -/
noncomputable def xi_hellinger_kernel_rkhs_volume_section {kappa : Nat} (s : Fin kappa → ℝ)
    (j : Fin kappa) : Fin kappa → ℝ :=
  fun i => xi_hellinger_kernel_rkhs_volume_kernel (s i) (s j)

/-- Evaluation at the sampled depth indexed by `i`. -/
def xi_hellinger_kernel_rkhs_volume_eval {kappa : Nat} (i : Fin kappa) (f : Fin kappa → ℝ) : ℝ :=
  f i

/-- The finite Hellinger Gram matrix of the sampled kernel sections. -/
noncomputable def xi_hellinger_kernel_rkhs_volume_gram {kappa : Nat} (s : Fin kappa → ℝ) :
    Matrix (Fin kappa) (Fin kappa) ℝ :=
  fun i j => xi_hellinger_kernel_rkhs_volume_kernel (s i) (s j)

/-- The squared volume of the sampled kernel family, defined by its Gram determinant. -/
noncomputable def xi_hellinger_kernel_rkhs_volume_squared_volume {kappa : Nat}
    (s : Fin kappa → ℝ) : ℝ :=
  Matrix.det (xi_hellinger_kernel_rkhs_volume_gram s)

/-- The finite-dimensional RKHS surrogate records the closed Fourier form of the kernel, the
reproducing evaluation of the translated kernel sections, and the Gram-determinant volume formula.
-/
def xi_hellinger_kernel_rkhs_volume_statement {kappa : Nat} (s : Fin kappa → ℝ) : Prop :=
  (∀ x y : ℝ,
      xi_hellinger_kernel_rkhs_volume_kernel x y =
        Real.pi ^ 2 / (Real.cosh (Real.pi * (x - y))) ^ 2) ∧
    (∀ i j : Fin kappa,
      xi_hellinger_kernel_rkhs_volume_eval i
          (xi_hellinger_kernel_rkhs_volume_section s j) =
        xi_hellinger_kernel_rkhs_volume_kernel (s i) (s j)) ∧
    xi_hellinger_kernel_rkhs_volume_squared_volume s =
      Matrix.det (xi_hellinger_kernel_rkhs_volume_gram s)

/-- Paper label: `prop:xi-hellinger-kernel-rkhs-volume`. The explicit `sech²` Fourier density
gives a concrete RKHS surrogate on every finite sample set, with the expected evaluation and
Gram-determinant volume identities. -/
theorem paper_xi_hellinger_kernel_rkhs_volume {kappa : Nat} (s : Fin kappa → ℝ) :
    xi_hellinger_kernel_rkhs_volume_statement s := by
  rcases paper_xi_hellinger_kernel_fourier_sech2 with ⟨hfourier, _⟩
  refine ⟨?_, ?_, rfl⟩
  · intro x y
    simpa [xi_hellinger_kernel_rkhs_volume_kernel] using hfourier (x - y)
  · intro i j
    rfl

end Omega.Zeta
