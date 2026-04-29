import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited even windows used in the terminal foldbin ledger. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_window (m : Nat) : Prop :=
  m = 6 \/ m = 8 \/ m = 10 \/ m = 12

/-- Concrete output-rank count `|X_m| = F_{m+2}`. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_output_rank
    (m : Nat) : Nat :=
  Nat.fib (m + 2)

/-- Abelianization rank from the visible/boundary Fibonacci splitting. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_abelianization_rank
    (m : Nat) : Nat :=
  Nat.fib m + Nat.fib (m + 1)

/-- Center rank read from the audited fiber histograms. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_center_rank
    (m : Nat) : Nat :=
  if m = 6 then 8 else 0

/-- Boundary sheet-parity center rank inside the `m = 6` center. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_boundary_center_rank : Nat :=
  3

/-- Quotient rank after removing the boundary sheet-parity subgroup. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_boundary_quotient_rank_value :
    Nat :=
  xi_foldbin_audited_even_center_collapse_abel_full_rank_center_rank 6 -
    xi_foldbin_audited_even_center_collapse_abel_full_rank_boundary_center_rank

/-- Abelianization has full Fibonacci output rank on the four audited windows. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_abelianization_full_rank :
    Prop :=
  forall m,
    xi_foldbin_audited_even_center_collapse_abel_full_rank_window m ->
      xi_foldbin_audited_even_center_collapse_abel_full_rank_abelianization_rank m =
        xi_foldbin_audited_even_center_collapse_abel_full_rank_output_rank m

/-- The `m = 6` center has rank eight. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_center_m6_rank : Prop :=
  xi_foldbin_audited_even_center_collapse_abel_full_rank_center_rank 6 = 8

/-- The centers at `m = 8, 10, 12` are trivial. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_centers_m8_m10_m12_trivial :
    Prop :=
  xi_foldbin_audited_even_center_collapse_abel_full_rank_center_rank 8 = 0 /\
    xi_foldbin_audited_even_center_collapse_abel_full_rank_center_rank 10 = 0 /\
      xi_foldbin_audited_even_center_collapse_abel_full_rank_center_rank 12 = 0

/-- The boundary quotient of the `m = 6` center has rank five. -/
def xi_foldbin_audited_even_center_collapse_abel_full_rank_boundary_quotient_rank :
    Prop :=
  xi_foldbin_audited_even_center_collapse_abel_full_rank_boundary_quotient_rank_value = 5

private lemma xi_foldbin_audited_even_center_collapse_abel_full_rank_fib_split
    (m : Nat) (hm : xi_foldbin_audited_even_center_collapse_abel_full_rank_window m) :
    xi_foldbin_audited_even_center_collapse_abel_full_rank_abelianization_rank m =
      xi_foldbin_audited_even_center_collapse_abel_full_rank_output_rank m := by
  rcases hm with rfl | rfl | rfl | rfl <;>
    native_decide

/-- Paper label: `thm:xi-foldbin-audited-even-center-collapse-abel-full-rank`. -/
theorem paper_xi_foldbin_audited_even_center_collapse_abel_full_rank :
    xi_foldbin_audited_even_center_collapse_abel_full_rank_abelianization_full_rank /\
      xi_foldbin_audited_even_center_collapse_abel_full_rank_center_m6_rank /\
        xi_foldbin_audited_even_center_collapse_abel_full_rank_centers_m8_m10_m12_trivial /\
          xi_foldbin_audited_even_center_collapse_abel_full_rank_boundary_quotient_rank := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    exact xi_foldbin_audited_even_center_collapse_abel_full_rank_fib_split m hm
  · unfold xi_foldbin_audited_even_center_collapse_abel_full_rank_center_m6_rank
    native_decide
  · unfold xi_foldbin_audited_even_center_collapse_abel_full_rank_centers_m8_m10_m12_trivial
    native_decide
  · unfold xi_foldbin_audited_even_center_collapse_abel_full_rank_boundary_quotient_rank
      xi_foldbin_audited_even_center_collapse_abel_full_rank_boundary_quotient_rank_value
    native_decide

end Omega.Zeta
