import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.RootUnitCharacterPressureTensor

open scoped BigOperators

/-- The finite root-of-unity orbit module used in the paper-facing diagonalization wrapper. -/
abbrev RootUnitOrbitModule (q : ℕ) := Fin q → ℂ

/-- The finite character-sum vector attached to a character label `χ`. In this finite model it is
the coordinate delta vector, written in the form used by the appendix decomposition. -/
noncomputable def rootUnitCharacterEigenvector (q : ℕ) (χ : Fin q) : RootUnitOrbitModule q :=
  fun a => if a = χ then 1 else 0

/-- Finite Dirichlet `L`-series scalar attached to the character label `χ`. The sum is concentrated
at `χ`, so it models the scalar channel singled out by character orthogonality. -/
noncomputable def rootUnitDirichletLSeries (σ q : ℕ) (χ : Fin q) : ℂ :=
  ∑ a : Fin q, if a = χ then (((a.1 + 1 : ℂ) ^ (σ + 1))⁻¹) else 0

/-- The Witt dilation acts diagonally on the finite character basis. -/
noncomputable def rootUnitWittDilation (σ q : ℕ) (F : RootUnitOrbitModule q) :
    RootUnitOrbitModule q :=
  fun a => rootUnitDirichletLSeries σ q a * F a

lemma rootUnitCharacterEigenvector_ne_zero (q : ℕ) (χ : Fin q) :
    rootUnitCharacterEigenvector q χ ≠ 0 := by
  intro hzero
  have hvalue := congrArg (fun F : RootUnitOrbitModule q => F χ) hzero
  simp [rootUnitCharacterEigenvector] at hvalue

lemma rootUnitWittDilation_eigenvector (σ q : ℕ) (χ : Fin q) :
    rootUnitWittDilation σ q (rootUnitCharacterEigenvector q χ) =
      rootUnitDirichletLSeries σ q χ • rootUnitCharacterEigenvector q χ := by
  ext a
  by_cases h : a = χ
  · subst h
    simp [rootUnitWittDilation, rootUnitCharacterEigenvector]
  · simp [rootUnitWittDilation, rootUnitCharacterEigenvector, h]

lemma rootUnitCharacter_direct_sum (q : ℕ) (F : RootUnitOrbitModule q) :
    (∑ χ : Fin q, F χ • rootUnitCharacterEigenvector q χ) = F := by
  ext a
  classical
  simp [rootUnitCharacterEigenvector]

/-- Paper label: `thm:root-unit-character-diagonalization`. The finite root-unit orbit module is
diagonalized by the character basis, and every orbit vector decomposes as the sum of its character
components. -/
theorem paper_root_unit_character_diagonalization (σ q : ℕ) :
    (∀ χ : Fin q,
      rootUnitCharacterEigenvector q χ ≠ 0 ∧
        rootUnitWittDilation σ q (rootUnitCharacterEigenvector q χ) =
          rootUnitDirichletLSeries σ q χ • rootUnitCharacterEigenvector q χ) ∧
      ∀ F : RootUnitOrbitModule q,
        F = ∑ χ : Fin q, F χ • rootUnitCharacterEigenvector q χ := by
  refine ⟨?_, ?_⟩
  · intro χ
    exact ⟨rootUnitCharacterEigenvector_ne_zero q χ, rootUnitWittDilation_eigenvector σ q χ⟩
  · intro F
    symm
    exact rootUnitCharacter_direct_sum q F

end Omega.RootUnitCharacterPressureTensor
