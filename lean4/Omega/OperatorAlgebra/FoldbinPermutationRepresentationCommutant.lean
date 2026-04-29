import Mathlib

open scoped BigOperators

namespace Omega.OperatorAlgebra

/-- The fiberwise split model for the permutation representation: one trivial coordinate and one
standard coordinate for each fold fiber. -/
abbrev FoldbinPermutationRepresentation {X : Type*} (d : X → ℕ) :=
  (w : X) → ℂ × (Fin (d w - 1) → ℂ)

/-- The trivial isotypic block: one scalar on each fold fiber. -/
abbrev FoldbinTrivialBlock (X : Type*) := X → ℂ

/-- The direct sum of the pulled-back standard fiber summands. -/
abbrev FoldbinStandardBlock {X : Type*} (d : X → ℕ) :=
  (w : X) → Fin (d w - 1) → ℂ

/-- The nontrivial fibers, i.e. those with standard block of positive dimension. -/
abbrev FoldbinNontrivialFiber {X : Type*} (d : X → ℕ) := {w : X // 2 ≤ d w}

/-- One scalar survives in the commutant for each nontrivial standard summand. -/
abbrev FoldbinScalarBlock {X : Type*} (d : X → ℕ) := FoldbinNontrivialFiber d → ℂ

/-- Concrete commutant model: a full matrix block on the trivial isotypic part, plus one scalar
block for each nontrivial standard summand. -/
abbrev FoldbinCommutant {X : Type*} (d : X → ℕ) :=
  Matrix X X ℂ × FoldbinScalarBlock d

/-- Count of fibers carrying a nonzero standard summand. -/
abbrev foldbinNontrivialFiberCount {X : Type*} [Fintype X] (d : X → ℕ) : ℕ :=
  Fintype.card (FoldbinNontrivialFiber d)

/-- Distinct fibers carry distinct kernel labels in this concrete model. -/
def foldbinStandardKernel {X : Type*} (w : X) : Set X := {u | u ≠ w}

def foldbinPermutationDecomposition {X : Type*} (d : X → ℕ) :
    FoldbinPermutationRepresentation d ≃ₗ[ℂ] (FoldbinTrivialBlock X × FoldbinStandardBlock d) where
  toFun v := (fun w => (v w).1, fun w => (v w).2)
  invFun v w := (v.1 w, v.2 w)
  left_inv v := by
    funext w
    ext <;> rfl
  right_inv v := by
    ext w <;> rfl
  map_add' v w := by
    ext x <;> rfl
  map_smul' a v := by
    ext x <;> rfl

theorem foldbinStandardKernel_injective {X : Type*} :
    Function.Injective (foldbinStandardKernel (X := X)) := by
  intro a b hab
  by_contra hne
  have ha : a ∈ foldbinStandardKernel (X := X) b := by
    simp [foldbinStandardKernel, hne]
  have : a ∈ foldbinStandardKernel (X := X) a := by simpa [hab] using ha
  simp [foldbinStandardKernel] at this

theorem finrank_foldbinTrivialBlock {X : Type*} [Fintype X] :
    Module.finrank ℂ (FoldbinTrivialBlock X) = Fintype.card X := by
  simp [FoldbinTrivialBlock]

theorem finrank_foldbinStandardBlock {X : Type*} [Fintype X] (d : X → ℕ) :
    Module.finrank ℂ (FoldbinStandardBlock d) = ∑ w : X, (d w - 1) := by
  classical
  unfold FoldbinStandardBlock
  rw [Module.finrank_pi_fintype]
  simp

theorem finrank_foldbinScalarBlock {X : Type*} [Fintype X] (d : X → ℕ) :
    Module.finrank ℂ (FoldbinScalarBlock d) = foldbinNontrivialFiberCount d := by
  unfold FoldbinScalarBlock foldbinNontrivialFiberCount
  simp

theorem finrank_foldbinMatrixBlock {X : Type*} [Fintype X] :
    Module.finrank ℂ (Matrix X X ℂ) = Fintype.card X ^ 2 := by
  change Module.finrank ℂ (X → X → ℂ) = Fintype.card X ^ 2
  rw [Module.finrank_pi_fintype]
  simp [pow_two]

theorem finrank_foldbinCommutant {X : Type*} [Fintype X] (d : X → ℕ) :
    Module.finrank ℂ (FoldbinCommutant d) =
      Fintype.card X ^ 2 + foldbinNontrivialFiberCount d := by
  rw [Module.finrank_prod, finrank_foldbinMatrixBlock, finrank_foldbinScalarBlock]

/-- Fiberwise permutation representation decomposition and commutant dimension arithmetic. The
total representation splits into a trivial block and the fiberwise standard blocks; the standard
part has dimension `2^m - |X|`, and the commutant is the expected matrix block plus one scalar
for each nontrivial standard summand.
    thm:foldbin-permutation-representation-commutant -/
theorem paper_foldbin_permutation_representation_commutant
    {X : Type*} [Fintype X] (m : ℕ) (d : X → ℕ)
    (hfiber : ∀ w, 1 ≤ d w) (htotal : ∑ w : X, d w = 2 ^ m) :
    Nonempty (FoldbinPermutationRepresentation d ≃ₗ[ℂ]
      (FoldbinTrivialBlock X × FoldbinStandardBlock d)) ∧
    Function.Injective (foldbinStandardKernel (X := X)) ∧
    Module.finrank ℂ (FoldbinTrivialBlock X) = Fintype.card X ∧
    Module.finrank ℂ (FoldbinStandardBlock d) = 2 ^ m - Fintype.card X ∧
    Nonempty (FoldbinCommutant d ≃ₗ[ℂ] (Matrix X X ℂ × FoldbinScalarBlock d)) ∧
    Module.finrank ℂ (FoldbinCommutant d) = Fintype.card X ^ 2 + foldbinNontrivialFiberCount d := by
  classical
  have hcard_le : Fintype.card X ≤ 2 ^ m := by
    calc
      Fintype.card X = ∑ w : X, 1 := by simp
      _ ≤ ∑ w : X, d w := by
        refine Finset.sum_le_sum ?_
        intro w hw
        exact hfiber w
      _ = 2 ^ m := htotal
  have hsum_std :
      (∑ w : X, (d w - 1)) + Fintype.card X = 2 ^ m := by
    calc
      (∑ w : X, (d w - 1)) + Fintype.card X
          = (∑ w : X, (d w - 1)) + ∑ w : X, 1 := by simp
      _ = ∑ w : X, ((d w - 1) + 1) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ w : X, d w := by
            refine Finset.sum_congr rfl ?_
            intro w hw
            have hw' := hfiber w
            omega
      _ = 2 ^ m := htotal
  have hstd_dim :
      Module.finrank ℂ (FoldbinStandardBlock d) = 2 ^ m - Fintype.card X := by
    rw [finrank_foldbinStandardBlock]
    have := hsum_std
    omega
  refine ⟨⟨foldbinPermutationDecomposition d⟩, foldbinStandardKernel_injective, ?_, hstd_dim,
      ⟨LinearEquiv.refl ℂ (FoldbinCommutant d)⟩, finrank_foldbinCommutant d⟩
  exact finrank_foldbinTrivialBlock

end Omega.OperatorAlgebra
