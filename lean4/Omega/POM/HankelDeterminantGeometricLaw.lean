import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete shifted Hankel data for the determinant propagation law. -/
structure POMHankelDeterminantGeometricLawData where
  d : ℕ
  k0 : ℕ
  H : ℕ → Matrix (Fin d) (Fin d) ℝ
  A : Matrix (Fin d) (Fin d) ℝ
  hshift : ∀ r, H (k0 + r) = H k0 * A ^ r

namespace POMHankelDeterminantGeometricLawData

/-- Determinant sequence `D_r = det(H_{k₀+r})`. -/
def determinantSequence (D : POMHankelDeterminantGeometricLawData) (r : ℕ) : ℝ :=
  (D.H (D.k0 + r)).det

/-- Paper-facing package: determinants propagate geometrically, hence satisfy the multiplicative
second-order recurrence. The recurrence is written in the shifted natural-number form
`D_{r+2} D_r = D_{r+1}^2`. -/
def package (D : POMHankelDeterminantGeometricLawData) : Prop :=
  (∀ r, D.determinantSequence r = (D.H D.k0).det * D.A.det ^ r) ∧
    ∀ r, D.determinantSequence (r + 2) * D.determinantSequence r =
      D.determinantSequence (r + 1) ^ 2

lemma determinant_sequence_geometric (D : POMHankelDeterminantGeometricLawData) :
    ∀ r, D.determinantSequence r = (D.H D.k0).det * D.A.det ^ r := by
  intro r
  unfold determinantSequence
  rw [D.hshift r, Matrix.det_mul, Matrix.det_pow]

lemma determinant_sequence_second_order (D : POMHankelDeterminantGeometricLawData) :
    ∀ r, D.determinantSequence (r + 2) * D.determinantSequence r =
      D.determinantSequence (r + 1) ^ 2 := by
  intro r
  let h0 := (D.H D.k0).det
  let a := D.A.det
  rw [D.determinant_sequence_geometric, D.determinant_sequence_geometric,
    D.determinant_sequence_geometric]
  simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

end POMHankelDeterminantGeometricLawData

open POMHankelDeterminantGeometricLawData

set_option maxHeartbeats 400000 in
/-- If the shifted Hankel family propagates by powers of `A`, then its determinant sequence is
geometric and therefore obeys the multiplicative second-order law
`D_{r+1} D_{r-1} = D_r^2`, written on `ℕ` as `D_{r+2} D_r = D_{r+1}^2`.
    cor:pom-hankel-determinant-geometric-law -/
theorem paper_pom_hankel_determinant_geometric_law (D : POMHankelDeterminantGeometricLawData) :
    D.package := by
  exact ⟨D.determinant_sequence_geometric, D.determinant_sequence_second_order⟩

end Omega.POM
