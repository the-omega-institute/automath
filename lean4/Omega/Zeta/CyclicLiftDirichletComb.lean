import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
import Omega.Zeta.RhStratificationSPlane

namespace Omega.Zeta

/-- The unit-modulus phase factor contributed by the `k`-th sector of a `q`-fold cyclic lift. -/
noncomputable def cyclicLiftPhase (q k : ℕ) : ℂ :=
  Complex.exp ((((2 : ℝ) * Real.pi * k) / q) * Complex.I)

/-- The imaginary coordinate of the `k`-th Dirichlet pole after a `q`-fold cyclic lift. -/
noncomputable def cyclicLiftPoleIm (lambda t : ℝ) (q k : ℕ) : ℝ :=
  (t + 2 * Real.pi * k) / (q * Real.log lambda)

@[simp] theorem norm_cyclicLiftPhase (q k : ℕ) : ‖cyclicLiftPhase q k‖ = 1 := by
  simpa [cyclicLiftPhase] using
    Complex.norm_exp_ofReal_mul_I ((((2 : ℝ) * Real.pi * k) / q))

/-- Paper label: `cor:zeta-cyclic-lift-dirichlet-comb`. -/
theorem paper_zeta_cyclic_lift_dirichlet_comb :
    (∀ lambda : ℝ, 1 < lambda → ∀ μ : ℂ, ∀ q k : ℕ,
      rhSPlaneRe lambda (μ * cyclicLiftPhase q k) = rhSPlaneRe lambda μ) ∧
    (∀ lambda t : ℝ, ∀ q k : ℕ, 1 < lambda → 0 < q →
      cyclicLiftPoleIm lambda t q (k + 1) - cyclicLiftPoleIm lambda t q k =
        2 * Real.pi / (q * Real.log lambda)) ∧
    (∀ lambda : ℝ, 1 < lambda → ∀ μ : ℂ, ∀ q k : ℕ,
      (‖μ‖ ≤ Real.sqrt lambda ↔ ‖μ * cyclicLiftPhase q k‖ ≤ Real.sqrt lambda)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro lambda hlambda μ q k
    simp [rhSPlaneRe]
  · intro lambda t q k hlambda hq
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    have hlog : Real.log lambda ≠ 0 := (Real.log_pos hlambda).ne'
    unfold cyclicLiftPoleIm
    field_simp [hq', hlog]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  · intro lambda hlambda μ q k
    constructor <;> intro h
    · simpa [norm_mul] using h
    · simpa [norm_mul] using h

end Omega.Zeta
