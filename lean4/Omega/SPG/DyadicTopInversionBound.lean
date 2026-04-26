import Mathlib.Tactic

namespace Omega.SPG

/-- Top-cell count of a dyadic resolution at scale `m`, dimension `n`.
    thm:spg-dyadic-top-dimensional-holographic-inversion-exponential-ill-conditioning -/
def topCellCount (m n : ℕ) : ℕ := 2 ^ (m * n)

/-- Symbolic form of the top-cell count.
    thm:spg-dyadic-top-dimensional-holographic-inversion-exponential-ill-conditioning -/
theorem topCellCount_eq_pow (m n : ℕ) : topCellCount m n = 2 ^ (m * n) := rfl

/-- Boundary-cell count: `2n` faces of dimension-one lower resolution.
    thm:spg-dyadic-top-dimensional-holographic-inversion-exponential-ill-conditioning -/
def boundaryCellCount (m n : ℕ) : ℕ := 2 * n * 2 ^ (m * (n - 1))

/-- Symbolic form of the boundary-cell count.
    thm:spg-dyadic-top-dimensional-holographic-inversion-exponential-ill-conditioning -/
theorem boundaryCellCount_eq (m n : ℕ) :
    boundaryCellCount m n = 2 * n * 2 ^ (m * (n - 1)) := rfl

/-- Boundary-to-top ratio exposes the exponential ill-conditioning of the
    dyadic top-dimensional holographic inversion problem: it collapses like
    `2n / 2^m` in the scale parameter `m`.
    thm:spg-dyadic-top-dimensional-holographic-inversion-exponential-ill-conditioning -/
theorem boundary_ratio_eq (m n : ℕ) (hn : 1 ≤ n) :
    (boundaryCellCount m n : ℝ) / (topCellCount m n : ℝ) =
      (2 * n : ℝ) / 2 ^ m := by
  unfold boundaryCellCount topCellCount
  have hsplit : m * n = m + m * (n - 1) := by
    have : n = (n - 1) + 1 := by omega
    calc m * n = m * ((n - 1) + 1) := by rw [← this]
      _ = m * (n - 1) + m := by ring
      _ = m + m * (n - 1) := by ring
  rw [hsplit, pow_add]
  push_cast
  have h2pow_ne : (2 : ℝ) ^ m ≠ 0 := by positivity
  have h2pow_sub_ne : (2 : ℝ) ^ (m * (n - 1)) ≠ 0 := by positivity
  field_simp

/-- Paper-facing statement alias for the dyadic top-dimensional holographic inversion
exponential ill-conditioning package. -/
def spg_dyadic_top_dimensional_holographic_inversion_exponential_ill_conditioning_statement :
    Prop :=
  (∀ m n : ℕ, topCellCount m n = 2 ^ (m * n)) ∧
    (∀ m n : ℕ, boundaryCellCount m n = 2 * n * 2 ^ (m * (n - 1))) ∧
    (∀ m n : ℕ, 1 ≤ n →
      (boundaryCellCount m n : ℝ) / (topCellCount m n : ℝ) = (2 * n : ℝ) / 2 ^ m) ∧
    (∀ m : ℕ,
      (boundaryCellCount m 2 : ℝ) / (topCellCount m 2 : ℝ) = (4 : ℝ) / 2 ^ m)

/-- Paper package: dyadic top-dimensional holographic inversion ill-conditioning
    numerical scaffolding.
    thm:spg-dyadic-top-dimensional-holographic-inversion-exponential-ill-conditioning -/
theorem paper_spg_dyadic_top_inversion_ill_conditioning :
    (∀ m n : ℕ, topCellCount m n = 2 ^ (m * n)) ∧
    (∀ m n : ℕ, boundaryCellCount m n = 2 * n * 2 ^ (m * (n - 1))) ∧
    (∀ m n : ℕ, 1 ≤ n →
      (boundaryCellCount m n : ℝ) / (topCellCount m n : ℝ) =
        (2 * n : ℝ) / 2 ^ m) ∧
    (∀ m : ℕ,
      (boundaryCellCount m 2 : ℝ) / (topCellCount m 2 : ℝ) =
        (4 : ℝ) / 2 ^ m) := by
  refine ⟨topCellCount_eq_pow, boundaryCellCount_eq, boundary_ratio_eq, ?_⟩
  intro m
  rw [boundary_ratio_eq m 2 (by omega)]
  push_cast
  ring

/-- Paper label: `thm:spg-dyadic-top-dimensional-holographic-inversion-exponential-ill-conditioning`.
This is the paper-facing wrapper around the concrete top-cell, boundary-cell, and boundary-ratio
identities used to witness the exponential ill-conditioning. -/
theorem paper_spg_dyadic_top_dimensional_holographic_inversion_exponential_ill_conditioning :
    spg_dyadic_top_dimensional_holographic_inversion_exponential_ill_conditioning_statement := by
  exact paper_spg_dyadic_top_inversion_ill_conditioning

end Omega.SPG
