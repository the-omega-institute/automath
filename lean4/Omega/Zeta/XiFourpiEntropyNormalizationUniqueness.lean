import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Single-atom area after the locked residue normalization. -/
def xi_fourpi_entropy_normalization_uniqueness_single_atom_area (m : ℕ) (δ : ℝ) : ℝ :=
  4 * Real.pi * (m : ℝ) * δ / (1 + δ)

/-- Area-normalized entropy for a single atom. -/
def xi_fourpi_entropy_normalization_uniqueness_single_atom_entropy
    (lam : ℝ) (m : ℕ) (δ : ℝ) : ℝ :=
  xi_fourpi_entropy_normalization_uniqueness_single_atom_area m δ / lam

/-- The scalar that survives after the deep-defect limit `δ / (1 + δ) → 1`. -/
def xi_fourpi_entropy_normalization_uniqueness_deep_defect_scalar (lam : ℝ) : ℝ :=
  4 * Real.pi / lam

/-- Concrete uniqueness statement for the `4π` entropy normalization. -/
def xi_fourpi_entropy_normalization_uniqueness_statement : Prop :=
  (∀ m : ℕ, xi_fourpi_entropy_normalization_uniqueness_single_atom_area m 1 =
    2 * Real.pi * (m : ℝ)) ∧
  (∀ lam : ℝ, 0 < lam →
    (xi_fourpi_entropy_normalization_uniqueness_deep_defect_scalar lam = 1 ↔
      lam = 4 * Real.pi)) ∧
  (∀ (m : ℕ) (δ : ℝ), 0 < δ →
    xi_fourpi_entropy_normalization_uniqueness_single_atom_entropy (4 * Real.pi) m δ =
      (m : ℝ) * δ / (1 + δ))

/-- Paper label: `prop:xi-fourpi-entropy-normalization-uniqueness`. -/
theorem paper_xi_fourpi_entropy_normalization_uniqueness :
    xi_fourpi_entropy_normalization_uniqueness_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    unfold xi_fourpi_entropy_normalization_uniqueness_single_atom_area
    ring
  · intro lam hlam
    constructor
    · intro h
      have hlam_ne : lam ≠ 0 := hlam.ne'
      unfold xi_fourpi_entropy_normalization_uniqueness_deep_defect_scalar at h
      calc
        lam = lam * 1 := by ring
        _ = lam * (4 * Real.pi / lam) := by rw [h]
        _ = 4 * Real.pi := by field_simp [hlam_ne]
    · intro h
      unfold xi_fourpi_entropy_normalization_uniqueness_deep_defect_scalar
      rw [h]
      have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp [h4pi_ne]
  · intro m δ _hδ
    unfold xi_fourpi_entropy_normalization_uniqueness_single_atom_entropy
      xi_fourpi_entropy_normalization_uniqueness_single_atom_area
    have h4pi_ne : (4 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp [h4pi_ne]

end

end Omega.Zeta
