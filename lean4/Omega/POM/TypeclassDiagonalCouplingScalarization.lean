import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.POM.TypeclassDiagonalCouplingSeeds

namespace Omega.POM

noncomputable section

open scoped BigOperators

/-- The positive quadratic-root branch attached to the diagonal-coupling scalarization. -/
def pom_typeclass_diagonal_coupling_scalarization_root {α : Type*}
    (w : α → ℝ) (A κ : ℝ) (x : α) : ℝ :=
  if κ = 0 then
    w x / A
  else
    (Real.sqrt (A ^ 2 + 4 * κ * w x) - A) / (2 * κ)

/-- Scalar fixed-point map `A ↦ Σ_x u_x(A, κ)`. -/
def pom_typeclass_diagonal_coupling_scalarization_fixedPointMap {α : Type*} [Fintype α]
    (w : α → ℝ) (κ A : ℝ) : ℝ :=
  ∑ x, pom_typeclass_diagonal_coupling_scalarization_root w A κ x

/-- Gap function `A - Σ_x u_x(A, κ)`. -/
def pom_typeclass_diagonal_coupling_scalarization_gap {α : Type*} [Fintype α]
    (w : α → ℝ) (κ A : ℝ) : ℝ :=
  A - pom_typeclass_diagonal_coupling_scalarization_fixedPointMap w κ A

lemma pom_typeclass_diagonal_coupling_scalarization_root_quadratic {α : Type*}
    (w : α → ℝ) (A κ : ℝ) (x : α) (hw_pos : 0 < w x) (hA_pos : 0 < A) (hκ_nonneg : 0 ≤ κ) :
    κ * (pom_typeclass_diagonal_coupling_scalarization_root w A κ x) ^ 2 +
        A * pom_typeclass_diagonal_coupling_scalarization_root w A κ x =
      w x := by
  by_cases hκ : κ = 0
  · have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    simp [pom_typeclass_diagonal_coupling_scalarization_root, hκ]
    field_simp [hA_ne]
  · have hκ_pos : 0 < κ := lt_of_le_of_ne hκ_nonneg (Ne.symm hκ)
    have h2κ_ne : 2 * κ ≠ 0 := by nlinarith
    have h4κ_ne : 4 * κ ≠ 0 := by nlinarith
    have hκ_ne : κ ≠ 0 := by exact hκ
    have hdisc_nonneg : 0 ≤ A ^ 2 + 4 * κ * w x := by
      nlinarith [sq_nonneg A, hκ_pos, hw_pos]
    let s : ℝ := Real.sqrt (A ^ 2 + 4 * κ * w x)
    have hs_sq : s ^ 2 = A ^ 2 + 4 * κ * w x := by
      simp [s, hdisc_nonneg]
    calc
      κ * (pom_typeclass_diagonal_coupling_scalarization_root w A κ x) ^ 2 +
          A * pom_typeclass_diagonal_coupling_scalarization_root w A κ x =
        κ * (((s - A) / (2 * κ)) ^ 2) + A * ((s - A) / (2 * κ)) := by
          simp [pom_typeclass_diagonal_coupling_scalarization_root, hκ, s]
      _ = (s ^ 2 - A ^ 2) / (4 * κ) := by
          field_simp [h2κ_ne, h4κ_ne]
          ring
      _ = w x := by
          rw [hs_sq]
          field_simp [hκ_ne]
          ring_nf

lemma pom_typeclass_diagonal_coupling_scalarization_root_pos {α : Type*}
    (w : α → ℝ) (A κ : ℝ) (x : α) (hw_pos : 0 < w x) (hA_pos : 0 < A) (hκ_nonneg : 0 ≤ κ) :
    0 < pom_typeclass_diagonal_coupling_scalarization_root w A κ x := by
  by_cases hκ : κ = 0
  · simpa [pom_typeclass_diagonal_coupling_scalarization_root, hκ] using div_pos hw_pos hA_pos
  · have hκ_pos : 0 < κ := lt_of_le_of_ne hκ_nonneg (Ne.symm hκ)
    have hdisc_nonneg : 0 ≤ A ^ 2 + 4 * κ * w x := by
      nlinarith [sq_nonneg A, hκ_pos, hw_pos]
    have hdisc_gt : A ^ 2 < A ^ 2 + 4 * κ * w x := by
      nlinarith [hκ_pos, hw_pos]
    have hsqrt_gt : A < Real.sqrt (A ^ 2 + 4 * κ * w x) := by
      have hsqrt_sq : (Real.sqrt (A ^ 2 + 4 * κ * w x)) ^ 2 = A ^ 2 + 4 * κ * w x := by
        simp [hdisc_nonneg]
      have hsqrt_nonneg : 0 ≤ Real.sqrt (A ^ 2 + 4 * κ * w x) := Real.sqrt_nonneg _
      nlinarith
    have hnum_pos : 0 < Real.sqrt (A ^ 2 + 4 * κ * w x) - A := by
      linarith
    have hden_pos : 0 < 2 * κ := by
      nlinarith
    simpa [pom_typeclass_diagonal_coupling_scalarization_root, hκ] using div_pos hnum_pos hden_pos

/-- Paper label: `thm:pom-typeclass-diagonal-coupling-scalarization`.
For a nonnegative diagonal parameter `κ`, the explicit positive root solves the coordinatewise
quadratic marginal constraint, and any strictly monotone scalar gap function admits at most one
positive fixed point `A = Σ_x u_x(A, κ)`. -/
theorem paper_pom_typeclass_diagonal_coupling_scalarization {α : Type*} [Fintype α]
    (w : α → ℝ) (κ A : ℝ) (hw_pos : ∀ x, 0 < w x) (hA_pos : 0 < A) (hκ_nonneg : 0 ≤ κ)
    (hgap_strictMono :
      StrictMono fun t : ℝ => pom_typeclass_diagonal_coupling_scalarization_gap w κ t)
    (hA_fixed : A = pom_typeclass_diagonal_coupling_scalarization_fixedPointMap w κ A) :
    (∀ x,
      κ * (pom_typeclass_diagonal_coupling_scalarization_root w A κ x) ^ 2 +
          A * pom_typeclass_diagonal_coupling_scalarization_root w A κ x =
        w x) ∧
      (∀ x, 0 < pom_typeclass_diagonal_coupling_scalarization_root w A κ x) ∧
      ∃! t : ℝ,
        0 < t ∧
          t = pom_typeclass_diagonal_coupling_scalarization_fixedPointMap w κ t := by
  let _ :=
    Omega.POM.TypeclassDiagonalCouplingSeeds.paper_pom_typeclass_diagonal_coupling_package
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact pom_typeclass_diagonal_coupling_scalarization_root_quadratic
      w A κ x (hw_pos x) hA_pos hκ_nonneg
  · intro x
    exact pom_typeclass_diagonal_coupling_scalarization_root_pos
      w A κ x (hw_pos x) hA_pos hκ_nonneg
  · refine ⟨A, ⟨hA_pos, hA_fixed⟩, ?_⟩
    intro t ht
    have hgap_t : pom_typeclass_diagonal_coupling_scalarization_gap w κ t = 0 := by
      rcases ht with ⟨_, ht_fixed⟩
      unfold pom_typeclass_diagonal_coupling_scalarization_gap
      linarith
    have hgap_A : pom_typeclass_diagonal_coupling_scalarization_gap w κ A = 0 := by
      unfold pom_typeclass_diagonal_coupling_scalarization_gap
      linarith
    exact hgap_strictMono.injective (by rw [hgap_t, hgap_A])

end

end Omega.POM
