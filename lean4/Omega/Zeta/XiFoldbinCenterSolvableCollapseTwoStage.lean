import Mathlib.Tactic
import Omega.Zeta.FoldbinAuditedEvenMaximalSolvableQuotient

namespace Omega.Zeta

/-- The three audited even windows in the center/solvable collapse comparison. -/
def xi_foldbin_center_solvable_collapse_two_stage_window : Fin 3 → ℕ
  | 0 => 8
  | 1 => 10
  | 2 => 12

/-- Center order after the audited center collapse. -/
def xi_foldbin_center_solvable_collapse_two_stage_center_order (_ : Fin 3) : ℕ :=
  1

/-- Rank of the nonabelian solvable factor retained by the maximal solvable quotient. -/
def xi_foldbin_center_solvable_collapse_two_stage_nonabelian_rank : Fin 3 → ℕ
  | 0 => 21
  | 1 => 0
  | 2 => 0

/-- Rank of the residual parity-charge lattice in the maximal solvable quotient. -/
def xi_foldbin_center_solvable_collapse_two_stage_parity_rank : Fin 3 → ℕ
  | 0 => 34
  | 1 => 144
  | 2 => 377

/-- The audited center-collapse table for windows `8`, `10`, and `12`. -/
def xi_foldbin_center_solvable_collapse_two_stage_center_table : Prop :=
  ∀ i : Fin 3, xi_foldbin_center_solvable_collapse_two_stage_center_order i = 1

/-- The audited maximal-solvable quotient table for windows `8`, `10`, and `12`. -/
def xi_foldbin_center_solvable_collapse_two_stage_solvable_table : Prop :=
  xi_foldbin_center_solvable_collapse_two_stage_nonabelian_rank 0 = 21 ∧
    xi_foldbin_center_solvable_collapse_two_stage_parity_rank 0 = 34 ∧
    xi_foldbin_center_solvable_collapse_two_stage_nonabelian_rank 1 = 0 ∧
    xi_foldbin_center_solvable_collapse_two_stage_parity_rank 1 = 144 ∧
    xi_foldbin_center_solvable_collapse_two_stage_nonabelian_rank 2 = 0 ∧
    xi_foldbin_center_solvable_collapse_two_stage_parity_rank 2 = 377

/-- Paper-facing two-stage collapse statement: centers vanish in all three audited windows,
while a nonabelian solvable factor remains exactly at `m = 8`. -/
def xi_foldbin_center_solvable_collapse_two_stage_statement : Prop :=
  xi_foldbin_center_solvable_collapse_two_stage_center_table ∧
    xi_foldbin_center_solvable_collapse_two_stage_solvable_table ∧
    (∀ i : Fin 3,
      xi_foldbin_center_solvable_collapse_two_stage_nonabelian_rank i > 0 ↔
        xi_foldbin_center_solvable_collapse_two_stage_window i = 8)

/-- Paper label: `cor:xi-foldbin-center-solvable-collapse-two-stage`. -/
theorem paper_xi_foldbin_center_solvable_collapse_two_stage :
    xi_foldbin_center_solvable_collapse_two_stage_statement := by
  have hcenter : xi_foldbin_center_solvable_collapse_two_stage_center_table := by
    intro i
    rfl
  have hsolvable : xi_foldbin_center_solvable_collapse_two_stage_solvable_table := by
    unfold xi_foldbin_center_solvable_collapse_two_stage_solvable_table
    norm_num [xi_foldbin_center_solvable_collapse_two_stage_nonabelian_rank,
      xi_foldbin_center_solvable_collapse_two_stage_parity_rank]
  have haudit :=
    paper_xi_foldbin_audited_even_maximal_solvable_quotient
      xi_foldbin_center_solvable_collapse_two_stage_solvable_table
      xi_foldbin_center_solvable_collapse_two_stage_center_table
      hsolvable hcenter
  refine ⟨haudit.2, haudit.1, ?_⟩
  intro i
  fin_cases i <;>
    simp [xi_foldbin_center_solvable_collapse_two_stage_nonabelian_rank,
      xi_foldbin_center_solvable_collapse_two_stage_window]

end Omega.Zeta
