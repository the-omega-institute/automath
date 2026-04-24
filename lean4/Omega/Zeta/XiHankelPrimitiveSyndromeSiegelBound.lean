import Mathlib.NumberTheory.SiegelsLemma
import Omega.Zeta.XiHankelCofactorSyndromeSingleCoordinate

namespace Omega.Zeta

open Matrix

attribute [local instance] Matrix.seminormedAddCommGroup

/-- Paper label: `thm:xi-hankel-primitive-syndrome-siegel-bound`. A full-rank `ρ × (d + 1)` row
submatrix of a Hankel block falls under Siegel's lemma, yielding a nonzero integral kernel witness
with the expected sup-norm bound. In corank one, the last adjugate column of the square Hankel
block gives the concrete cofactor syndrome, whose last coordinate is the principal minor and which
is nonzero as soon as that minor is nonzero. -/
theorem paper_xi_hankel_primitive_syndrome_siegel_bound
    (ρ d : ℕ) (hρ : 0 < ρ) (hρd : ρ < d + 1)
    (A : Matrix (Fin ρ) (Fin (d + 1)) ℤ) (hA : A ≠ 0) (a : Fin (2 * d + 1) → ℤ) :
    (∃ s : Fin (d + 1) → ℤ,
        s ≠ 0 ∧
          A.mulVec s = 0 ∧
            ‖s‖ ≤ (((d + 1 : ℕ) : ℝ) * ‖A‖) ^ ((ρ : ℝ) / ((d + 1 : ℝ) - ρ)) ) ∧
      ((xi_hankel_cofactor_syndrome_single_coordinate_hankel_matrix ℤ d a).det = 0 →
        let u := xi_hankel_cofactor_syndrome_single_coordinate_cofactor_column ℤ d a
        let H0 := xi_hankel_cofactor_syndrome_single_coordinate_principal_matrix ℤ d a
        (xi_hankel_cofactor_syndrome_single_coordinate_hankel_matrix ℤ d a).mulVec u = 0 ∧
          u (Fin.last d) = H0.det ∧
          (H0.det ≠ 0 → u ≠ 0) ∧
          u (Fin.last d) ∣ H0.det) := by
  refine ⟨?_, ?_⟩
  · have hcard : Fintype.card (Fin ρ) < Fintype.card (Fin (d + 1)) := by
      simpa [Fintype.card_fin] using hρd
    have hpos : 0 < Fintype.card (Fin ρ) := by
      simpa [Fintype.card_fin] using hρ
    simpa [Fintype.card_fin] using Int.Matrix.exists_ne_zero_int_vec_norm_le' A hcard hpos hA
  · intro hdet
    let u := xi_hankel_cofactor_syndrome_single_coordinate_cofactor_column ℤ d a
    let H0 := xi_hankel_cofactor_syndrome_single_coordinate_principal_matrix ℤ d a
    have hcofactor := paper_xi_hankel_cofactor_syndrome_single_coordinate ℤ d a hdet
    simpa [u, H0] using hcofactor

end Omega.Zeta
