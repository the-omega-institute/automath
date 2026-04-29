import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Fixed dyadic resolution parameters for the finite moment box. -/
structure xi_time_part9fa_dyadic_finite_moment_completeness_data where
  m : ℕ
  n : ℕ

/-- Cells in the `2^m` grid of the `n`-cube. -/
abbrev xi_time_part9fa_dyadic_finite_moment_completeness_cell
    (D : xi_time_part9fa_dyadic_finite_moment_completeness_data) : Type :=
  Fin D.n → Fin (2 ^ D.m)

/-- A dyadic polycube at fixed resolution, represented by its occupied cells. -/
abbrev xi_time_part9fa_dyadic_finite_moment_completeness_polycube
    (D : xi_time_part9fa_dyadic_finite_moment_completeness_data) : Type :=
  Finset (xi_time_part9fa_dyadic_finite_moment_completeness_cell D)

/-- The finite moment box separates cells by recording the occupancy of every grid cell. -/
def xi_time_part9fa_dyadic_finite_moment_completeness_moment_box
    (D : xi_time_part9fa_dyadic_finite_moment_completeness_data)
    (U : xi_time_part9fa_dyadic_finite_moment_completeness_polycube D) :
    xi_time_part9fa_dyadic_finite_moment_completeness_cell D → Prop :=
  fun c => c ∈ U

/-- Fixed-resolution completeness: the finite box of cell moments determines the polycube. -/
def xi_time_part9fa_dyadic_finite_moment_completeness_statement
    (D : xi_time_part9fa_dyadic_finite_moment_completeness_data) : Prop :=
  Function.Injective (xi_time_part9fa_dyadic_finite_moment_completeness_moment_box D)

/-- Paper label: `thm:xi-time-part9fa-dyadic-finite-moment-completeness`. -/
theorem paper_xi_time_part9fa_dyadic_finite_moment_completeness
    (D : xi_time_part9fa_dyadic_finite_moment_completeness_data) :
    xi_time_part9fa_dyadic_finite_moment_completeness_statement D := by
  intro U V hUV
  ext c
  exact iff_of_eq (congrFun hUV c)

end Omega.Zeta
