import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Carathéodory kernel attached to a complex-valued field. -/
def xi_carath_imag_constant_invisible_kernel (C : ℂ → ℂ) (w z : ℂ) : ℂ :=
  (C w + star (C z)) / (1 - w * star z)

/-- Adding a purely imaginary constant to the Carathéodory field. -/
def xi_carath_imag_constant_invisible_shift (C : ℂ → ℂ) (η : ℝ) : ℂ → ℂ :=
  fun w => C w + Complex.I * (η : ℂ)

/-- Finite Gram matrix extracted from the Carathéodory kernel. -/
def xi_carath_imag_constant_invisible_gram
    {n : ℕ} (C : ℂ → ℂ) (nodes : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => xi_carath_imag_constant_invisible_kernel C (nodes i) (nodes j)

/-- Paper label: `prop:xi-carath-imag-constant-invisible`. Adding a purely imaginary constant
changes neither the Carathéodory kernel nor any finite Gram matrix extracted from it, so every
Toeplitz inertia invariant built from those matrices is unchanged as well. -/
theorem paper_xi_carath_imag_constant_invisible
    (C : ℂ → ℂ) (η : ℝ) :
    (∀ w z,
      xi_carath_imag_constant_invisible_kernel
          (xi_carath_imag_constant_invisible_shift C η) w z =
        xi_carath_imag_constant_invisible_kernel C w z) ∧
      (∀ {n : ℕ} (nodes : Fin n → ℂ),
        xi_carath_imag_constant_invisible_gram
            (xi_carath_imag_constant_invisible_shift C η) nodes =
          xi_carath_imag_constant_invisible_gram C nodes) := by
  have hkernel :
      ∀ w z,
        xi_carath_imag_constant_invisible_kernel
            (xi_carath_imag_constant_invisible_shift C η) w z =
          xi_carath_imag_constant_invisible_kernel C w z := by
    intro w z
    simp [xi_carath_imag_constant_invisible_kernel,
      xi_carath_imag_constant_invisible_shift, add_assoc, add_comm]
  refine ⟨hkernel, ?_⟩
  · intro n nodes
    ext i j
    exact hkernel (nodes i) (nodes j)

end

end Omega.Zeta
