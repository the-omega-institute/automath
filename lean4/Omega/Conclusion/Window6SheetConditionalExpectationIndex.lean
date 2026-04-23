import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The concrete `2 × 2` boundary block used for the window-`6` sheet expectation. -/
abbrev conclusion_window6_sheet_conditional_expectation_index_boundary_block :=
  Fin 2 → Fin 2 → ℂ

/-- The global audited window-`6` algebra: three boundary `2 × 2` blocks and eighteen scalar
non-boundary summands. -/
abbrev conclusion_window6_sheet_conditional_expectation_index_a6 :=
  (Fin 3 → conclusion_window6_sheet_conditional_expectation_index_boundary_block) ×
    (Fin 18 → ℂ)

/-- Conjugation by `P_w = diag(1,-1)` on the concrete `2 × 2` coordinates. -/
def conclusion_window6_sheet_conditional_expectation_index_p_conj
    (a : conclusion_window6_sheet_conditional_expectation_index_boundary_block) :
    conclusion_window6_sheet_conditional_expectation_index_boundary_block :=
  fun i j =>
    if i = j then a i j else -a i j

/-- Left multiplication by `X_w = [[0,1],[1,0]]`: it swaps the two rows. -/
def conclusion_window6_sheet_conditional_expectation_index_x_left
    (a : conclusion_window6_sheet_conditional_expectation_index_boundary_block) :
    conclusion_window6_sheet_conditional_expectation_index_boundary_block :=
  fun i j => a ⟨1 - i.1, by omega⟩ j

/-- Projection onto the diagonal `P_w`-fixed subalgebra. -/
def conclusion_window6_sheet_conditional_expectation_index_diag_projection
    (a : conclusion_window6_sheet_conditional_expectation_index_boundary_block) :
    conclusion_window6_sheet_conditional_expectation_index_boundary_block :=
  fun i j => if i = j then a i i else 0

/-- The boundary conditional expectation `a ↦ (a + P_w a P_w)/2`, recorded in coordinates. -/
noncomputable def conclusion_window6_sheet_conditional_expectation_index_boundary_expectation
    (a : conclusion_window6_sheet_conditional_expectation_index_boundary_block) :
    conclusion_window6_sheet_conditional_expectation_index_boundary_block :=
  fun i j =>
    ((a i j) + conclusion_window6_sheet_conditional_expectation_index_p_conj a i j) / 2

/-- The global sheet expectation: boundary blocks are averaged against `P_w`, non-boundary blocks
are unchanged. -/
noncomputable def conclusion_window6_sheet_conditional_expectation_index_e_sheet
    (A : conclusion_window6_sheet_conditional_expectation_index_a6) :
    conclusion_window6_sheet_conditional_expectation_index_a6 :=
  (fun w =>
      conclusion_window6_sheet_conditional_expectation_index_boundary_expectation (A.1 w), A.2)

/-- The boundary target algebra consists of the `P_w`-fixed diagonal blocks. -/
def conclusion_window6_sheet_conditional_expectation_index_b6 :
    Set conclusion_window6_sheet_conditional_expectation_index_a6 :=
  {A | ∀ w,
      conclusion_window6_sheet_conditional_expectation_index_p_conj (A.1 w) = A.1 w}

/-- The central boundary idempotent `p_bdry`: `1` on the three boundary blocks and `0` on the
eighteen non-boundary blocks. -/
def conclusion_window6_sheet_conditional_expectation_index_p_bdry :
    (Fin 3 → ℂ) × (Fin 18 → ℂ) :=
  (fun _ => 1, fun _ => 0)

/-- The central unit of the direct-sum model. -/
def conclusion_window6_sheet_conditional_expectation_index_one :
    (Fin 3 → ℂ) × (Fin 18 → ℂ) :=
  (fun _ => 1, fun _ => 1)

/-- The blockwise Watatani index element: `2` on each boundary block and `1` elsewhere. -/
def conclusion_window6_sheet_conditional_expectation_index_index :
    (Fin 3 → ℂ) × (Fin 18 → ℂ) :=
  (fun _ => 2, fun _ => 1)

theorem conclusion_window6_sheet_conditional_expectation_index_boundary_expectation_eq_diag
    (a : conclusion_window6_sheet_conditional_expectation_index_boundary_block) :
    conclusion_window6_sheet_conditional_expectation_index_boundary_expectation a =
      conclusion_window6_sheet_conditional_expectation_index_diag_projection a := by
  funext i j
  by_cases hij : i = j
  · subst hij
    simp [conclusion_window6_sheet_conditional_expectation_index_boundary_expectation,
      conclusion_window6_sheet_conditional_expectation_index_diag_projection,
      conclusion_window6_sheet_conditional_expectation_index_p_conj]
  · simp [conclusion_window6_sheet_conditional_expectation_index_boundary_expectation,
      conclusion_window6_sheet_conditional_expectation_index_diag_projection,
      conclusion_window6_sheet_conditional_expectation_index_p_conj, hij]

theorem conclusion_window6_sheet_conditional_expectation_index_boundary_fixed
    (a : conclusion_window6_sheet_conditional_expectation_index_boundary_block) :
    conclusion_window6_sheet_conditional_expectation_index_p_conj
        (conclusion_window6_sheet_conditional_expectation_index_boundary_expectation a) =
      conclusion_window6_sheet_conditional_expectation_index_boundary_expectation a := by
  rw [conclusion_window6_sheet_conditional_expectation_index_boundary_expectation_eq_diag]
  funext i j
  by_cases hij : i = j
  · subst hij
    simp [conclusion_window6_sheet_conditional_expectation_index_diag_projection,
      conclusion_window6_sheet_conditional_expectation_index_p_conj]
  · simp [conclusion_window6_sheet_conditional_expectation_index_diag_projection,
      conclusion_window6_sheet_conditional_expectation_index_p_conj, hij]

theorem conclusion_window6_sheet_conditional_expectation_index_boundary_idempotent
    (a : conclusion_window6_sheet_conditional_expectation_index_boundary_block) :
    conclusion_window6_sheet_conditional_expectation_index_boundary_expectation
        (conclusion_window6_sheet_conditional_expectation_index_boundary_expectation a) =
      conclusion_window6_sheet_conditional_expectation_index_boundary_expectation a := by
  rw [conclusion_window6_sheet_conditional_expectation_index_boundary_expectation_eq_diag]
  funext i j
  by_cases hij : i = j
  · subst hij
    simp [conclusion_window6_sheet_conditional_expectation_index_boundary_expectation,
      conclusion_window6_sheet_conditional_expectation_index_diag_projection,
      conclusion_window6_sheet_conditional_expectation_index_p_conj]
  · simp [conclusion_window6_sheet_conditional_expectation_index_boundary_expectation,
      conclusion_window6_sheet_conditional_expectation_index_diag_projection,
      conclusion_window6_sheet_conditional_expectation_index_p_conj, hij]

theorem conclusion_window6_sheet_conditional_expectation_index_boundary_quasibasis
    (a : conclusion_window6_sheet_conditional_expectation_index_boundary_block) :
    conclusion_window6_sheet_conditional_expectation_index_boundary_expectation a +
        conclusion_window6_sheet_conditional_expectation_index_x_left
          (conclusion_window6_sheet_conditional_expectation_index_boundary_expectation
            (conclusion_window6_sheet_conditional_expectation_index_x_left a)) =
      a := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [conclusion_window6_sheet_conditional_expectation_index_boundary_expectation,
      conclusion_window6_sheet_conditional_expectation_index_p_conj,
      conclusion_window6_sheet_conditional_expectation_index_x_left]

theorem conclusion_window6_sheet_conditional_expectation_index_e_sheet_mem_b6
    (A : conclusion_window6_sheet_conditional_expectation_index_a6) :
    conclusion_window6_sheet_conditional_expectation_index_e_sheet A ∈
      conclusion_window6_sheet_conditional_expectation_index_b6 := by
  intro w
  exact conclusion_window6_sheet_conditional_expectation_index_boundary_fixed (A.1 w)

theorem conclusion_window6_sheet_conditional_expectation_index_e_sheet_idempotent
    (A : conclusion_window6_sheet_conditional_expectation_index_a6) :
    conclusion_window6_sheet_conditional_expectation_index_e_sheet
        (conclusion_window6_sheet_conditional_expectation_index_e_sheet A) =
      conclusion_window6_sheet_conditional_expectation_index_e_sheet A := by
  ext w i <;> simp [conclusion_window6_sheet_conditional_expectation_index_e_sheet,
    conclusion_window6_sheet_conditional_expectation_index_boundary_idempotent]

theorem conclusion_window6_sheet_conditional_expectation_index_index_eq_one_add_p_bdry :
    conclusion_window6_sheet_conditional_expectation_index_index =
      conclusion_window6_sheet_conditional_expectation_index_one +
        conclusion_window6_sheet_conditional_expectation_index_p_bdry := by
  ext i
  · simp [conclusion_window6_sheet_conditional_expectation_index_index,
      conclusion_window6_sheet_conditional_expectation_index_one,
      conclusion_window6_sheet_conditional_expectation_index_p_bdry]
    norm_num
  · simp [conclusion_window6_sheet_conditional_expectation_index_index,
      conclusion_window6_sheet_conditional_expectation_index_one,
      conclusion_window6_sheet_conditional_expectation_index_p_bdry]

/-- Paper label: `thm:conclusion-window6-sheet-conditional-expectation-index`.
In the explicit `3·M₂(ℂ) ⊕ ℂ¹⁸` window-`6` model, the sheet expectation is the projection onto the
`P_w`-fixed diagonal boundary algebra, the Watatani quasi-basis on each boundary block is
`{I, X_w}`, non-boundary summands contribute the identity block, and the central index element is
`1 + p_bdry`. -/
theorem paper_conclusion_window6_sheet_conditional_expectation_index :
    (∀ a,
      conclusion_window6_sheet_conditional_expectation_index_boundary_expectation a =
        conclusion_window6_sheet_conditional_expectation_index_diag_projection a) ∧
    (∀ A,
      conclusion_window6_sheet_conditional_expectation_index_e_sheet A ∈
        conclusion_window6_sheet_conditional_expectation_index_b6) ∧
    (∀ A,
      conclusion_window6_sheet_conditional_expectation_index_e_sheet
          (conclusion_window6_sheet_conditional_expectation_index_e_sheet A) =
        conclusion_window6_sheet_conditional_expectation_index_e_sheet A) ∧
    (∀ a,
      conclusion_window6_sheet_conditional_expectation_index_boundary_expectation a +
          conclusion_window6_sheet_conditional_expectation_index_x_left
            (conclusion_window6_sheet_conditional_expectation_index_boundary_expectation
              (conclusion_window6_sheet_conditional_expectation_index_x_left a)) =
        a) ∧
    conclusion_window6_sheet_conditional_expectation_index_index =
      conclusion_window6_sheet_conditional_expectation_index_one +
        conclusion_window6_sheet_conditional_expectation_index_p_bdry := by
  refine ⟨conclusion_window6_sheet_conditional_expectation_index_boundary_expectation_eq_diag,
    conclusion_window6_sheet_conditional_expectation_index_e_sheet_mem_b6,
    conclusion_window6_sheet_conditional_expectation_index_e_sheet_idempotent,
    conclusion_window6_sheet_conditional_expectation_index_boundary_quasibasis,
    conclusion_window6_sheet_conditional_expectation_index_index_eq_one_add_p_bdry⟩

end Omega.Conclusion
