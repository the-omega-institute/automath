import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited window-`6` block degrees, ordered as `8` blocks of size `2`, `4` blocks of
size `3`, and `9` blocks of size `4`. -/
def xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree
    (i : Fin 21) : ℕ :=
  if (i : ℕ) < 8 then 2 else if (i : ℕ) < 12 then 3 else 4

/-- A finite-block Pimsner--Popa bound encoded by the maximal block degree. -/
def xi_time_part9ze_center_condexp_pimsner_popa_index_finiteBlockBound
    (Λ : ℕ) : Prop :=
  ∀ i : Fin 21, xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i ≤ Λ

/-- The concrete statement used for the fold-center conditional expectation index: the block
bound is `4`, a rank-one witness in a size-`4` block makes it sharp, and the resulting local
index differs from the global compression ratio `64 / 21`. -/
def xi_time_part9ze_center_condexp_pimsner_popa_index_statement : Prop :=
  xi_time_part9ze_center_condexp_pimsner_popa_index_finiteBlockBound 4 ∧
    xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree
        ⟨12, by norm_num⟩ = 4 ∧
      (∀ Λ : ℕ,
        xi_time_part9ze_center_condexp_pimsner_popa_index_finiteBlockBound Λ → 4 ≤ Λ) ∧
        ((64 : ℚ) / 21 ≠ 4)

/-- Scalar weighted center-index package: the already audited window-`6` Pimsner--Popa
maximum is `4`, while the scalar and doubled weighted normalizations evaluate to `64` and `32`.
-/
def xi_time_part9ze_scalar_weighted_center_condexp_indices_statement : Prop :=
  xi_time_part9ze_center_condexp_pimsner_popa_index_statement ∧
    ((64 : ℚ) / 16 =
      xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree
        ⟨12, by norm_num⟩) ∧
      ((64 : ℚ) / 1 = 64) ∧
        ((64 : ℚ) / 2 = 32) ∧
          ((32 : ℚ) / 8 =
            xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree
              ⟨12, by norm_num⟩)

lemma xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree_le_four
    (i : Fin 21) :
    xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree i ≤ 4 := by
  unfold xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree
  split_ifs <;> norm_num

/-- Paper label: `thm:xi-time-part9ze-center-condexp-pimsner-popa-index`. -/
theorem paper_xi_time_part9ze_center_condexp_pimsner_popa_index :
    xi_time_part9ze_center_condexp_pimsner_popa_index_statement := by
  refine
    ⟨xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree_le_four,
      ?_, ?_, ?_⟩
  · norm_num [xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree]
  · intro Λ hΛ
    have hblock := hΛ ⟨12, by norm_num⟩
    norm_num [xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree] at hblock
    exact hblock
  · norm_num

/-- Paper label: `thm:xi-time-part9ze-scalar-weighted-center-condexp-indices`. -/
theorem paper_xi_time_part9ze_scalar_weighted_center_condexp_indices :
    xi_time_part9ze_scalar_weighted_center_condexp_indices_statement := by
  refine ⟨paper_xi_time_part9ze_center_condexp_pimsner_popa_index, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree]
  · norm_num
  · norm_num
  · norm_num [xi_time_part9ze_center_condexp_pimsner_popa_index_window6FiberDegree]

end Omega.Zeta
