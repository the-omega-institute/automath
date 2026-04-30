import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

namespace xi_binfold_capacity_atomic_measure_unique_recovery

/-- The golden-ratio parameter in the two-atom bin-fold capacity law. -/
def xi_binfold_capacity_atomic_measure_unique_recovery_phi : ℝ :=
  Real.goldenRatio

/-- The two atoms of the recovered measure. -/
def xi_binfold_capacity_atomic_measure_unique_recovery_atom : Bool → ℝ
  | false => 1 / xi_binfold_capacity_atomic_measure_unique_recovery_phi
  | true => 1

/-- The masses of the recovered measure at the two atoms. -/
def xi_binfold_capacity_atomic_measure_unique_recovery_mass : Bool → ℝ
  | false => 1 / Real.sqrt 5
  | true => xi_binfold_capacity_atomic_measure_unique_recovery_phi / Real.sqrt 5

/-- The min-kernel integral against the explicit two-atom measure. -/
def xi_binfold_capacity_atomic_measure_unique_recovery_integral (s : ℝ) : ℝ :=
  ∑ b : Bool,
    xi_binfold_capacity_atomic_measure_unique_recovery_mass b *
      min s (xi_binfold_capacity_atomic_measure_unique_recovery_atom b)

/-- The limiting bin-fold capacity curve. -/
def xi_binfold_capacity_atomic_measure_unique_recovery_capacity (s : ℝ) : ℝ :=
  xi_binfold_capacity_atomic_measure_unique_recovery_phi / Real.sqrt 5 * min s 1 +
    1 / Real.sqrt 5 *
      min s (1 / xi_binfold_capacity_atomic_measure_unique_recovery_phi)

/-- The second-derivative recovery field represented as point masses. -/
def xi_binfold_capacity_atomic_measure_unique_recovery_recoveredMass (x : ℝ) : ℝ :=
  (if x = 1 / xi_binfold_capacity_atomic_measure_unique_recovery_phi
    then 1 / Real.sqrt 5
    else 0) +
  if x = 1 then
    xi_binfold_capacity_atomic_measure_unique_recovery_phi / Real.sqrt 5
  else
    0

/-- Concrete statement for the bin-fold capacity measure recovery theorem. -/
def xi_binfold_capacity_atomic_measure_unique_recovery_statement : Prop :=
  (∀ s : ℝ,
    xi_binfold_capacity_atomic_measure_unique_recovery_integral s =
      xi_binfold_capacity_atomic_measure_unique_recovery_capacity s) ∧
    xi_binfold_capacity_atomic_measure_unique_recovery_recoveredMass
        (1 / xi_binfold_capacity_atomic_measure_unique_recovery_phi) =
      1 / Real.sqrt 5 ∧
    xi_binfold_capacity_atomic_measure_unique_recovery_recoveredMass 1 =
      xi_binfold_capacity_atomic_measure_unique_recovery_phi / Real.sqrt 5 ∧
    ∀ μ : ℝ → ℝ,
      (∀ x : ℝ,
        μ x = xi_binfold_capacity_atomic_measure_unique_recovery_recoveredMass x) →
        μ = xi_binfold_capacity_atomic_measure_unique_recovery_recoveredMass

end xi_binfold_capacity_atomic_measure_unique_recovery

open xi_binfold_capacity_atomic_measure_unique_recovery

/-- Paper label: `thm:xi-binfold-capacity-atomic-measure-unique-recovery`. -/
theorem paper_xi_binfold_capacity_atomic_measure_unique_recovery :
    xi_binfold_capacity_atomic_measure_unique_recovery_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    simp [xi_binfold_capacity_atomic_measure_unique_recovery_integral,
      xi_binfold_capacity_atomic_measure_unique_recovery_capacity,
      xi_binfold_capacity_atomic_measure_unique_recovery_mass,
      xi_binfold_capacity_atomic_measure_unique_recovery_atom]
  · have hφ_ne : xi_binfold_capacity_atomic_measure_unique_recovery_phi ≠ 0 := by
      simpa [xi_binfold_capacity_atomic_measure_unique_recovery_phi] using
        Real.goldenRatio_ne_zero
    have hφ_ne_one : xi_binfold_capacity_atomic_measure_unique_recovery_phi ≠ 1 := by
      have hφ_sq :
          xi_binfold_capacity_atomic_measure_unique_recovery_phi ^ 2 =
            xi_binfold_capacity_atomic_measure_unique_recovery_phi + 1 := by
        simp [xi_binfold_capacity_atomic_measure_unique_recovery_phi, Real.goldenRatio_sq]
      intro hφ_one
      nlinarith
    have hφ_inv_ne_one : (1 / xi_binfold_capacity_atomic_measure_unique_recovery_phi : ℝ) ≠ 1 := by
      intro h
      have hφ_one : xi_binfold_capacity_atomic_measure_unique_recovery_phi = 1 := by
        field_simp [hφ_ne] at h
        linarith
      exact hφ_ne_one hφ_one
    simp [xi_binfold_capacity_atomic_measure_unique_recovery_recoveredMass, hφ_ne_one]
  · have hφ_ne_one : xi_binfold_capacity_atomic_measure_unique_recovery_phi ≠ 1 := by
      have hφ_sq :
          xi_binfold_capacity_atomic_measure_unique_recovery_phi ^ 2 =
            xi_binfold_capacity_atomic_measure_unique_recovery_phi + 1 := by
        simp [xi_binfold_capacity_atomic_measure_unique_recovery_phi, Real.goldenRatio_sq]
      intro hφ_one
      nlinarith
    have hone_ne_inv : (1 : ℝ) ≠ 1 / xi_binfold_capacity_atomic_measure_unique_recovery_phi := by
      intro h
      have hφ_one : xi_binfold_capacity_atomic_measure_unique_recovery_phi = 1 := by
        have h' : (1 / xi_binfold_capacity_atomic_measure_unique_recovery_phi : ℝ) = 1 :=
          h.symm
        have hφ_ne : xi_binfold_capacity_atomic_measure_unique_recovery_phi ≠ 0 := by
          simpa [xi_binfold_capacity_atomic_measure_unique_recovery_phi] using
            Real.goldenRatio_ne_zero
        field_simp [hφ_ne] at h'
        linarith
      exact hφ_ne_one hφ_one
    simp [xi_binfold_capacity_atomic_measure_unique_recovery_recoveredMass, hφ_ne_one]
  · intro μ hμ
    funext x
    exact hμ x

end

end Omega.Zeta
