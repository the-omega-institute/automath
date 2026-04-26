import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The audited ξ-scaling map `φ_m`. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi (m : ℝ) (z : ℂ) : ℂ :=
  (m : ℂ) * z

/-- A homogeneous ratio encoding the mutual interaction term. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_rho (z w : ℂ) : ℝ :=
  Complex.normSq (z - w) / Complex.normSq (z + w)

/-- The Poisson self term attached to a point in the upper half-plane. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term (z : ℂ) : ℝ :=
  Real.log z.im

/-- Total self-energy of a finite configuration. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_energy
    (A : Finset ℂ) : ℝ :=
  Finset.sum A xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term

/-- Self-energy after applying `φ_m` pointwise. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_self_energy
    (A : Finset ℂ) (m : ℝ) : ℝ :=
  Finset.sum A fun z =>
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term
      (xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi m z)

/-- Mutual interaction energy of the finite pair `(A, B)`. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_mutual_energy
    (A B : Finset ℂ) : ℝ :=
  Finset.sum A fun z =>
    Finset.sum B fun w => xi_scaling_mutual_energy_conservation_selfenergy_dissipation_rho z w

/-- Mutual interaction energy after scaling both configurations by `φ_m`. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_mutual_energy
    (A B : Finset ℂ) (m : ℝ) : ℝ :=
  Finset.sum A fun z =>
    Finset.sum B fun w =>
      xi_scaling_mutual_energy_conservation_selfenergy_dissipation_rho
        (xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi m z)
        (xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi m w)

/-- Positivity hypotheses ensuring the self-energy logarithms are defined on the scaled
configurations. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_hypotheses
    (A B : Finset ℂ) (m : ℝ) : Prop :=
  0 < m ∧ (∀ z ∈ A, 0 < z.im) ∧ (∀ z ∈ B, 0 < z.im)

/-- Under positive scaling, every self term acquires one additive `log m` while the homogeneous
mutual interaction remains unchanged. -/
def xi_scaling_mutual_energy_conservation_selfenergy_dissipation_conclusion
    (A B : Finset ℂ) (m : ℝ) : Prop :=
  xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_self_energy A m =
      (A.card : ℝ) * Real.log m +
        xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_energy A ∧
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_self_energy B m =
      (B.card : ℝ) * Real.log m +
        xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_energy B ∧
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_mutual_energy A B m =
      xi_scaling_mutual_energy_conservation_selfenergy_dissipation_mutual_energy A B

private lemma xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term_scale
    {m : ℝ} {z : ℂ} (hm : 0 < m) (hz : 0 < z.im) :
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term
        (xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi m z) =
      Real.log m +
        xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term z := by
  unfold xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi
  rw [show (((m : ℂ) * z).im) = m * z.im by simp]
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt hz)]

private lemma xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_self_energy_eq
    (A : Finset ℂ) {m : ℝ} (hm : 0 < m) (hA : ∀ z ∈ A, 0 < z.im) :
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_self_energy A m =
      (A.card : ℝ) * Real.log m +
        xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_energy A := by
  unfold xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_self_energy
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_energy
  calc
    Finset.sum A
        (fun z =>
          xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term
            (xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi m z)) =
      Finset.sum A
        (fun z =>
          Real.log m +
            xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term z) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          exact
            xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term_scale hm
              (hA z hz)
    _ =
        Finset.sum A (fun _z => Real.log m) +
          Finset.sum A
            xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term := by
          rw [Finset.sum_add_distrib]
    _ =
        (A.card : ℝ) * Real.log m +
          Finset.sum A
            xi_scaling_mutual_energy_conservation_selfenergy_dissipation_self_term := by
          simp

private lemma xi_scaling_mutual_energy_conservation_selfenergy_dissipation_rho_scale
    {m : ℝ} (hm : 0 < m) (z w : ℂ) :
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_rho
        (xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi m z)
        (xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi m w) =
      xi_scaling_mutual_energy_conservation_selfenergy_dissipation_rho z w := by
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hm_sq_ne : m * m ≠ 0 := mul_ne_zero hm_ne hm_ne
  unfold xi_scaling_mutual_energy_conservation_selfenergy_dissipation_rho
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_phi
  rw [show ((m : ℂ) * z - (m : ℂ) * w) = (m : ℂ) * (z - w) by ring]
  rw [show ((m : ℂ) * z + (m : ℂ) * w) = (m : ℂ) * (z + w) by ring]
  rw [Complex.normSq_mul, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal]
  by_cases hden : Complex.normSq (z + w) = 0
  · simp [hden]
  · field_simp [hm_sq_ne, hden]

private lemma xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_mutual_energy_eq
    (A B : Finset ℂ) {m : ℝ} (hm : 0 < m) :
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_mutual_energy A B m =
      xi_scaling_mutual_energy_conservation_selfenergy_dissipation_mutual_energy A B := by
  unfold xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_mutual_energy
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_mutual_energy
  refine Finset.sum_congr rfl ?_
  intro z hz
  refine Finset.sum_congr rfl ?_
  intro w hw
  exact xi_scaling_mutual_energy_conservation_selfenergy_dissipation_rho_scale hm z w

/-- Scaling by `φ_m` preserves the homogeneous mutual interaction energy, while each finite
self-energy ledger acquires exactly one additive `log m` per point.
    thm:xi-scaling-mutual-energy-conservation-selfenergy-dissipation -/
theorem paper_xi_scaling_mutual_energy_conservation_selfenergy_dissipation
    (A B : Finset ℂ) (m : ℝ)
    (h : xi_scaling_mutual_energy_conservation_selfenergy_dissipation_hypotheses A B m) :
    xi_scaling_mutual_energy_conservation_selfenergy_dissipation_conclusion A B m := by
  rcases h with ⟨hm, hA, hB⟩
  refine ⟨?_, ?_, ?_⟩
  · exact
      xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_self_energy_eq A hm hA
  · exact
      xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_self_energy_eq B hm hB
  · exact
      xi_scaling_mutual_energy_conservation_selfenergy_dissipation_scaled_mutual_energy_eq A B hm

end

end Omega.Zeta
