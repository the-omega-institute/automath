import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
import Omega.GU.M11Z34RotationPartComplexStructure

open scoped BigOperators

namespace Omega.GU

/-- The primitive `34`-th root used by the canonical complex realization of the `m = 11`
rotation part. -/
noncomputable def m11Canonical34Root : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 34)

/-- The `i`-th complex eigenvalue in the plane-by-plane diagonalization. -/
noncomputable def m11Canonical16ComplexWeight (i : Fin 16) : ℂ :=
  m11Canonical34Root ^ (i.1 + 1)

/-- The determinant of the canonical `16`-dimensional complex module, expressed as the product of
its diagonal eigenvalues. -/
noncomputable def m11Canonical16ComplexDet : ℂ :=
  ∏ i : Fin 16, m11Canonical16ComplexWeight i

lemma m11_canonical_16_exponent_sum : ((∑ i : Fin 16, ((i : ℕ) + 1 : ℕ)) : ℕ) = 136 := by
  simpa using
    (show ((Finset.univ : Finset (Fin 16)).sum fun i => ((i : ℕ) + 1 : ℕ)) = 136 by native_decide)

lemma m11Canonical34Root_pow_34 : m11Canonical34Root ^ 34 = 1 := by
  calc
    m11Canonical34Root ^ 34 = Complex.exp (34 * (2 * Real.pi * Complex.I / 34)) := by
      simp [m11Canonical34Root, ← Complex.exp_nat_mul]
    _ = Complex.exp (2 * Real.pi * Complex.I) := by
      field_simp
    _ = 1 := by simpa [two_mul] using Complex.exp_two_pi_mul_I

lemma m11Canonical16ComplexDet_eq_root_pow :
    m11Canonical16ComplexDet = m11Canonical34Root ^ 136 := by
  unfold m11Canonical16ComplexDet m11Canonical16ComplexWeight
  rw [Finset.prod_pow_eq_pow_sum]
  exact congrArg (fun n : ℕ => m11Canonical34Root ^ n) m11_canonical_16_exponent_sum

lemma m11Canonical16ComplexDet_eq_one : m11Canonical16ComplexDet = 1 := by
  rw [m11Canonical16ComplexDet_eq_root_pow, show (136 : ℕ) = 34 * 4 by norm_num, pow_mul,
    m11Canonical34Root_pow_34, one_pow]

/-- The canonical `m = 11` / `\ZZ₃₄` complex module uses the `16` real rotation planes as
complex lines, carries the diagonal action by the roots `ζ, ζ², …, ζ¹⁶`, and the total
determinant is `ζ^(1+⋯+16) = ζ^136 = (ζ^34)^4 = 1`.
    prop:m11-canonical-16-complex-module-det-one -/
theorem paper_m11_canonical_16_complex_module_det_one :
    cBoundaryCount 11 = 34 ∧
    Nat.fib 9 = 34 ∧
    z34RotationPlaneCount = 16 ∧
    z34RotationPlaneDimension = 2 ∧
    (∀ i : Fin 16, m11Canonical16ComplexWeight i = m11Canonical34Root ^ (i.1 + 1)) ∧
    m11Canonical16ComplexDet = 1 := by
  rcases paper_m11_z34_rotation_part_complex_structure with
    ⟨hBoundary, hFib, hPlanes, hDim, _, _, _⟩
  refine ⟨hBoundary, hFib, hPlanes, hDim, ?_, m11Canonical16ComplexDet_eq_one⟩
  intro i
  rfl

end Omega.GU
