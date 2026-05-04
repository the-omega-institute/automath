import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The time used by the continued-fraction denominator `q`. -/
def xi_time_part60ae_diophantine_singular_ring_approximation_time (q : ℕ) : ℝ :=
  Real.pi * q

/-- The second-coordinate phase error after writing `α q = p + err`. -/
def xi_time_part60ae_diophantine_singular_ring_approximation_error
    (α err : ℝ) (p q : ℕ) : Prop :=
  α * q = (p : ℝ) + err

/-- A reusable quadratic cosine estimate at a small phase. -/
lemma xi_time_part60ae_diophantine_singular_ring_approximation_cos_quadratic
    (x : ℝ) :
    |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  have hupper : Real.cos x ≤ 1 := Real.cos_le_one x
  have hlower : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  rw [abs_of_nonpos (sub_nonpos.mpr hupper)]
  linarith

/-- Paper-facing concrete statement for
`thm:xi-time-part60ae-diophantine-singular-ring-approximation`.

If a convergent-style approximation is recorded as `α q = p + err` with
`|err| < qNext⁻¹`, then the first coordinate lands exactly on a corner sign, the
second coordinate is the same corner sign multiplied by the small residual phase,
and the cosine defect is quadratic in that residual phase. -/
def xi_time_part60ae_diophantine_singular_ring_approximation_statement : Prop :=
  ∀ (α err : ℝ) (p q qNext : ℕ),
    0 < qNext →
      xi_time_part60ae_diophantine_singular_ring_approximation_error α err p q →
        |err| < (qNext : ℝ)⁻¹ →
          Real.cos (xi_time_part60ae_diophantine_singular_ring_approximation_time q) =
              (-1 : ℝ) ^ q ∧
            Real.cos (Real.pi * (α * q)) =
              (-1 : ℝ) ^ p * Real.cos (Real.pi * err) ∧
            |Real.cos (Real.pi * err) - 1| ≤ (Real.pi * err) ^ 2 / 2 ∧
            |err| < (qNext : ℝ)⁻¹

/-- Paper label: `thm:xi-time-part60ae-diophantine-singular-ring-approximation`. -/
theorem paper_xi_time_part60ae_diophantine_singular_ring_approximation :
    xi_time_part60ae_diophantine_singular_ring_approximation_statement := by
  intro α err p q qNext _hqNext happrox herr
  refine ⟨?_, ?_, ?_, herr⟩
  · unfold xi_time_part60ae_diophantine_singular_ring_approximation_time
    simpa [mul_comm] using Real.cos_nat_mul_pi q
  · unfold xi_time_part60ae_diophantine_singular_ring_approximation_error at happrox
    have hangle : Real.pi * (α * q) = Real.pi * err + p * Real.pi := by
      rw [happrox]
      ring
    rw [hangle]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      Real.cos_add_nat_mul_pi (Real.pi * err) p
  · exact xi_time_part60ae_diophantine_singular_ring_approximation_cos_quadratic
      (Real.pi * err)

end

end Omega.Zeta
