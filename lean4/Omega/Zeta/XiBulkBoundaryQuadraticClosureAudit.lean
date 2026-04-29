import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A concrete `O(1)` predicate for functions compared on the logarithmic range `m ≥ 2`. -/
def xi_bulk_boundary_quadratic_closure_audit_bounded_error (F G : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m → |F m - G m| ≤ C

/-- Concrete statement for `cor:xi-bulk-boundary-quadratic-closure-audit`. -/
def xi_bulk_boundary_quadratic_closure_audit_statement : Prop :=
  ∀ (κ : ℝ) (Sbulk Sgen : ℕ → ℝ),
    xi_bulk_boundary_quadratic_closure_audit_bounded_error Sbulk
        (fun m => κ ^ (2 : ℕ) * Real.log (m : ℝ)) →
      (∀ m : ℕ, Sgen m = κ * Real.log (m : ℝ)) →
      xi_bulk_boundary_quadratic_closure_audit_bounded_error Sbulk
        (fun m => Sgen m ^ (2 : ℕ) / Real.log (m : ℝ))

lemma xi_bulk_boundary_quadratic_closure_audit_quadratic_identity
    (κ : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    (κ * Real.log (m : ℝ)) ^ (2 : ℕ) / Real.log (m : ℝ) =
      κ ^ (2 : ℕ) * Real.log (m : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlog_pos : 0 < Real.log (m : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hm)
  field_simp [ne_of_gt hlog_pos]

/-- Paper label: `cor:xi-bulk-boundary-quadratic-closure-audit`. -/
theorem paper_xi_bulk_boundary_quadratic_closure_audit :
    xi_bulk_boundary_quadratic_closure_audit_statement := by
  intro κ Sbulk Sgen hbulk hlinear
  rcases hbulk with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro m hm
  have hquad :
      Sgen m ^ (2 : ℕ) / Real.log (m : ℝ) = κ ^ (2 : ℕ) * Real.log (m : ℝ) := by
    rw [hlinear m]
    exact xi_bulk_boundary_quadratic_closure_audit_quadratic_identity κ hm
  simpa [hquad] using hC m hm

end Omega.Zeta
