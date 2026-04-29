import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The midpoint gate attached to the two adjacent Fourier amplitudes. -/
def xi_time_part9p1_midpoint_gate_cascade_critical_radius_midpoint_gate
    (left right : ℂ) : ℂ :=
  (left + right) / 2

/-- The finite gate product through the first `n` midpoint gates. -/
def xi_time_part9p1_midpoint_gate_cascade_critical_radius_product
    (left right : ℕ → ℂ) (n : ℕ) : ℂ :=
  Finset.prod (Finset.range n) fun i =>
    xi_time_part9p1_midpoint_gate_cascade_critical_radius_midpoint_gate (left i) (right i)

/-- The prefixed midpoint-gate cascade recurrence. -/
def xi_time_part9p1_midpoint_gate_cascade_critical_radius_cascade
    (left right : ℕ → ℂ) (z₀ : ℂ) : ℕ → ℂ
  | 0 => z₀
  | n + 1 =>
      xi_time_part9p1_midpoint_gate_cascade_critical_radius_cascade left right z₀ n *
        xi_time_part9p1_midpoint_gate_cascade_critical_radius_midpoint_gate (left n) (right n)

/-- The finite critical resonance radius is represented by the corresponding cascade product. -/
def xi_time_part9p1_midpoint_gate_cascade_critical_radius_radius
    (left right : ℕ → ℂ) (n : ℕ) : ℂ :=
  xi_time_part9p1_midpoint_gate_cascade_critical_radius_product left right n

/-- Concrete paper-facing package: the recurrence has the finite product solution, a zero midpoint
gate annihilates the cascade, and the same zero factor forces the packaged critical radius to
vanish. -/
def xi_time_part9p1_midpoint_gate_cascade_critical_radius_statement : Prop :=
  (∀ (left right : ℕ → ℂ) (z₀ : ℂ) (n : ℕ),
      xi_time_part9p1_midpoint_gate_cascade_critical_radius_cascade left right z₀ n =
        xi_time_part9p1_midpoint_gate_cascade_critical_radius_product left right n * z₀) ∧
    (∀ (left right : ℕ → ℂ) (z₀ : ℂ) (n : ℕ),
      (∃ i, i < n ∧
        xi_time_part9p1_midpoint_gate_cascade_critical_radius_midpoint_gate
          (left i) (right i) = 0) →
      xi_time_part9p1_midpoint_gate_cascade_critical_radius_cascade left right z₀ n = 0) ∧
    (∀ (left right : ℕ → ℂ) (n : ℕ),
      (∃ i, i < n ∧
        xi_time_part9p1_midpoint_gate_cascade_critical_radius_midpoint_gate
          (left i) (right i) = 0) →
      xi_time_part9p1_midpoint_gate_cascade_critical_radius_radius left right n = 0)

/-- The closed product form of the finite midpoint-gate cascade. -/
theorem xi_time_part9p1_midpoint_gate_cascade_critical_radius_product_formula
    (left right : ℕ → ℂ) (z₀ : ℂ) (n : ℕ) :
    xi_time_part9p1_midpoint_gate_cascade_critical_radius_cascade left right z₀ n =
      xi_time_part9p1_midpoint_gate_cascade_critical_radius_product left right n * z₀ := by
  induction n with
  | zero =>
      simp [xi_time_part9p1_midpoint_gate_cascade_critical_radius_cascade,
        xi_time_part9p1_midpoint_gate_cascade_critical_radius_product]
  | succ n ih =>
      simp [xi_time_part9p1_midpoint_gate_cascade_critical_radius_cascade,
        xi_time_part9p1_midpoint_gate_cascade_critical_radius_product, Finset.prod_range_succ,
        ih, mul_left_comm, mul_comm]

/-- Paper label: `thm:xi-time-part9p1-midpoint-gate-cascade-critical-radius`. -/
theorem paper_xi_time_part9p1_midpoint_gate_cascade_critical_radius :
    xi_time_part9p1_midpoint_gate_cascade_critical_radius_statement := by
  unfold xi_time_part9p1_midpoint_gate_cascade_critical_radius_statement
  refine ⟨?_, ?_, ?_⟩
  · exact fun left right z₀ n =>
      xi_time_part9p1_midpoint_gate_cascade_critical_radius_product_formula left right z₀ n
  · intro left right z₀ n hzero
    have hproduct :
        xi_time_part9p1_midpoint_gate_cascade_critical_radius_product left right n = 0 := by
      rcases hzero with ⟨i, hi, hgate⟩
      exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) hgate
    rw [xi_time_part9p1_midpoint_gate_cascade_critical_radius_product_formula left right z₀ n,
      hproduct, zero_mul]
  · intro left right n hzero
    unfold xi_time_part9p1_midpoint_gate_cascade_critical_radius_radius
    rcases hzero with ⟨i, hi, hgate⟩
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) hgate

end

end Omega.Zeta
