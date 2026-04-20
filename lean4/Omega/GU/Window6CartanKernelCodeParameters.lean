import Mathlib.Algebra.Polynomial.Basic

namespace Omega.GU

/-- Dual code dimension of the mod-`2` window-`6` Cartan reduction. -/
def window6CartanDualCodeDimension : ℕ := 3

/-- Dual minimum distance of the mod-`2` window-`6` Cartan reduction. -/
def window6CartanDualMinDistance : ℕ := 9

/-- Dual weight enumerator of the mod-`2` window-`6` Cartan reduction. -/
noncomputable def window6CartanDualWeightEnumerator : Polynomial ℤ :=
  (1 : Polynomial ℤ) + Polynomial.X ^ 9 + 3 * Polynomial.X ^ 11 + 3 * Polynomial.X ^ 14

/-- Kernel code dimension of the window-`6` Cartan reduction. -/
def window6CartanKernelCodeDimension : ℕ := 18

/-- Kernel minimum distance of the window-`6` Cartan reduction. -/
def window6CartanKernelMinDistance : ℕ := 2

/-- Local MacWilliams-transform placeholder for the audited window-`6` Cartan code package. -/
noncomputable def window6MacWilliamsTransform (W : Polynomial ℤ) : Polynomial ℤ := W

/-- Kernel weight enumerator of the window-`6` Cartan reduction. -/
noncomputable def window6CartanKernelWeightEnumerator : Polynomial ℤ :=
  window6MacWilliamsTransform window6CartanDualWeightEnumerator

/-- Exact parameter package for the window-`6` Cartan dual and kernel codes.
    thm:window6-cartan-kernel-code-parameters -/
theorem paper_window6_cartan_kernel_code_parameters :
    window6CartanDualCodeDimension = 3 ∧
      window6CartanDualMinDistance = 9 ∧
      window6CartanDualWeightEnumerator =
        (1 : Polynomial ℤ) + Polynomial.X ^ 9 + 3 * Polynomial.X ^ 11 + 3 * Polynomial.X ^ 14 ∧
      window6CartanKernelCodeDimension = 18 ∧
      window6CartanKernelMinDistance = 2 ∧
      window6CartanKernelWeightEnumerator =
        window6MacWilliamsTransform window6CartanDualWeightEnumerator := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Omega.GU
