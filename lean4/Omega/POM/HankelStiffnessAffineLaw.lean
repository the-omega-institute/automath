import Mathlib.Tactic
import Omega.POM.HankelDeterminantGeometricLaw

namespace Omega.POM

/-- Concrete data for the `p`-adic stiffness affine law. The Hankel determinant sequence is the
one from the geometric propagation theorem, and `valuation` is any multiplicative valuation on the
ground scalar model. -/
structure pom_hankel_stiffness_affine_law_Data where
  hankelData : POMHankelDeterminantGeometricLawData
  valuation : ℝ → ℤ
  hvaluation_mul : ∀ x y : ℝ, valuation (x * y) = valuation x + valuation y
  hvaluation_pow : ∀ x : ℝ, ∀ r : ℕ, valuation (x ^ r) = (r : ℤ) * valuation x

namespace pom_hankel_stiffness_affine_law_Data

/-- The shifted stiffness profile is affine with slope `v(det A)`. -/
def pom_hankel_stiffness_affine_law_affineStiffness
    (D : pom_hankel_stiffness_affine_law_Data) : Prop :=
  ∀ r : ℕ,
    D.valuation (D.hankelData.determinantSequence r) =
      D.valuation (D.hankelData.determinantSequence 0) +
        (r : ℤ) * D.valuation D.hankelData.A.det

end pom_hankel_stiffness_affine_law_Data

open pom_hankel_stiffness_affine_law_Data

/-- Paper label: `cor:pom-hankel-stiffness-affine-law`. -/
theorem paper_pom_hankel_stiffness_affine_law
    (D : pom_hankel_stiffness_affine_law_Data) :
    D.pom_hankel_stiffness_affine_law_affineStiffness := by
  intro r
  have hzero :
      D.valuation (D.hankelData.determinantSequence 0) =
        D.valuation (D.hankelData.H D.hankelData.k0).det := by
    rw [D.hankelData.determinant_sequence_geometric]
    simp
  rw [D.hankelData.determinant_sequence_geometric r, hzero]
  calc
    D.valuation ((D.hankelData.H D.hankelData.k0).det * D.hankelData.A.det ^ r)
        =
          D.valuation (D.hankelData.H D.hankelData.k0).det +
            (r : ℤ) * D.valuation D.hankelData.A.det := by
            rw [D.hvaluation_mul, D.hvaluation_pow]
    _ =
          D.valuation (D.hankelData.H D.hankelData.k0).det +
            (r : ℤ) * D.valuation D.hankelData.A.det := rfl

end Omega.POM
