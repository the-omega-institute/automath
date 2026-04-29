import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace Omega.Zeta

abbrev xi_hankel_primitive_gap_vanishing_criterion_space (n : ℕ) := Fin n → ℚ

/-- Concrete finite-dimensional Hankel/nullspace package for the primitive-gap vanishing test.
The Hankel operator acts on the `n`-dimensional coefficient space, the truncated-multiple space is
modeled by an injective copy of `ℚ^(n-d)`, and the codomain has dimension `d`, so rank-nullity
forces the kernel dimension to be `n-d`. -/
structure xi_hankel_primitive_gap_vanishing_criterion_data where
  n : ℕ
  d : ℕ
  hdn : d ≤ n
  hankelMap :
    xi_hankel_primitive_gap_vanishing_criterion_space n →ₗ[ℚ] Fin d → ℚ
  truncatedMultiples :
    Submodule ℚ (xi_hankel_primitive_gap_vanishing_criterion_space n)
  truncatedModel :
    (Fin (n - d) → ℚ) →ₗ[ℚ] xi_hankel_primitive_gap_vanishing_criterion_space n
  truncatedModel_injective : Function.Injective truncatedModel
  truncatedModel_range : truncatedModel.range = truncatedMultiples
  truncatedMultiples_le_kernel : truncatedMultiples ≤ LinearMap.ker hankelMap
  hankel_full_rank : Module.finrank ℚ (LinearMap.range hankelMap) = d

namespace xi_hankel_primitive_gap_vanishing_criterion_data

def xi_hankel_primitive_gap_vanishing_criterion_kernel_view
    (D : xi_hankel_primitive_gap_vanishing_criterion_data) :
    Submodule ℚ (LinearMap.ker D.hankelMap) where
  carrier := {x | ((x : LinearMap.ker D.hankelMap) : xi_hankel_primitive_gap_vanishing_criterion_space D.n)
    ∈ D.truncatedMultiples}
  zero_mem' := by
    change (0 : xi_hankel_primitive_gap_vanishing_criterion_space D.n) ∈ D.truncatedMultiples
    exact D.truncatedMultiples.zero_mem
  add_mem' := by
    intro x y hx hy
    change
      (((x : xi_hankel_primitive_gap_vanishing_criterion_space D.n) +
          (y : xi_hankel_primitive_gap_vanishing_criterion_space D.n)) ∈
        D.truncatedMultiples)
    exact D.truncatedMultiples.add_mem hx hy
  smul_mem' := by
    intro a x hx
    change
      (a • (x : xi_hankel_primitive_gap_vanishing_criterion_space D.n)) ∈ D.truncatedMultiples
    exact D.truncatedMultiples.smul_mem a hx

abbrev xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient
    (D : xi_hankel_primitive_gap_vanishing_criterion_data) :=
  (LinearMap.ker D.hankelMap) ⧸ D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view

def xi_hankel_primitive_gap_vanishing_criterion_statement
    (D : xi_hankel_primitive_gap_vanishing_criterion_data) : Prop :=
  Module.finrank ℚ D.truncatedMultiples = D.n - D.d ∧
    Module.finrank ℚ (LinearMap.ker D.hankelMap) = D.n - D.d ∧
      (Module.finrank ℚ
          D.xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient = 0 ↔
        LinearMap.ker D.hankelMap = D.truncatedMultiples)

lemma xi_hankel_primitive_gap_vanishing_criterion_kernel_view_eq_top_iff
    (D : xi_hankel_primitive_gap_vanishing_criterion_data) :
    D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view = ⊤ ↔
      LinearMap.ker D.hankelMap = D.truncatedMultiples := by
  constructor
  · intro hTop
    apply le_antisymm
    · intro x hx
      have hxTop :
          (⟨x, hx⟩ : LinearMap.ker D.hankelMap) ∈
            D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view := by
        simp [hTop]
      exact hxTop
    · exact D.truncatedMultiples_le_kernel
  · intro hEq
    apply top_unique
    intro x hx
    change
      ((x : LinearMap.ker D.hankelMap) :
          xi_hankel_primitive_gap_vanishing_criterion_space D.n) ∈ D.truncatedMultiples
    simpa [hEq] using (x : LinearMap.ker D.hankelMap).2

lemma xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient_finrank_zero_iff
    (D : xi_hankel_primitive_gap_vanishing_criterion_data) :
    Module.finrank ℚ
        D.xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient = 0 ↔
      LinearMap.ker D.hankelMap = D.truncatedMultiples := by
  constructor
  · intro hZero
    have hSum :
        Module.finrank ℚ
            D.xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient +
          Module.finrank ℚ
            D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view =
            Module.finrank ℚ (LinearMap.ker D.hankelMap) := by
      simpa [xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient] using
        (Submodule.finrank_quotient_add_finrank
          (D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view))
    have hView :
        Module.finrank ℚ
            D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view =
          Module.finrank ℚ (LinearMap.ker D.hankelMap) := by
      rw [hZero, zero_add] at hSum
      exact hSum
    have hTop :
        D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view = ⊤ :=
      Submodule.eq_top_of_finrank_eq hView
    exact
      (D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view_eq_top_iff).mp hTop
  · intro hEq
    have hTop :
        D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view = ⊤ :=
      (D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view_eq_top_iff).mpr hEq
    change Module.finrank ℚ ((LinearMap.ker D.hankelMap) ⧸
      D.xi_hankel_primitive_gap_vanishing_criterion_kernel_view) = 0
    rw [hTop]
    have hSub :
        Subsingleton ((LinearMap.ker D.hankelMap) ⧸ (⊤ : Submodule ℚ (LinearMap.ker D.hankelMap))) :=
      by infer_instance
    exact
      (Module.finrank_zero_iff
        (R := ℚ)
        (M := (LinearMap.ker D.hankelMap) ⧸
          (⊤ : Submodule ℚ (LinearMap.ker D.hankelMap)))).2 hSub

end xi_hankel_primitive_gap_vanishing_criterion_data

open xi_hankel_primitive_gap_vanishing_criterion_data

/-- Paper label: `thm:xi-hankel-primitive-gap-vanishing-criterion`. The injective truncated
multiple model has dimension `n-d`; rank-nullity gives the same dimension for the Hankel kernel;
hence the primitive quotient has dimension zero exactly when the truncated-multiple space and the
kernel agree. -/
theorem paper_xi_hankel_primitive_gap_vanishing_criterion
    (D : xi_hankel_primitive_gap_vanishing_criterion_data) :
    xi_hankel_primitive_gap_vanishing_criterion_statement D := by
  have hTruncatedDim :
      Module.finrank ℚ D.truncatedMultiples = D.n - D.d := by
    rw [← D.truncatedModel_range]
    simpa using LinearMap.finrank_range_of_inj D.truncatedModel_injective
  have hKernelDim :
      Module.finrank ℚ (LinearMap.ker D.hankelMap) = D.n - D.d := by
    have hRankNullity := LinearMap.finrank_range_add_finrank_ker D.hankelMap
    rw [D.hankel_full_rank] at hRankNullity
    have hRankNullity' : D.d + Module.finrank ℚ (LinearMap.ker D.hankelMap) = D.n := by
      simpa [xi_hankel_primitive_gap_vanishing_criterion_space, Module.finrank_fin_fun] using
        hRankNullity
    omega
  exact ⟨hTruncatedDim, hKernelDim,
    D.xi_hankel_primitive_gap_vanishing_criterion_primitive_quotient_finrank_zero_iff⟩

end Omega.Zeta
