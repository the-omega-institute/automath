import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.SyncKernelWeighted.PrimitiveCompletionHatp

namespace Omega.SyncKernelWeighted

open Omega.UnitCirclePhaseArithmetic
open scoped ArithmeticFunction.Moebius BigOperators
open scoped Polynomial

/-- The descended Chebyshev polynomial acting on completed coordinates, now viewed over `ℚ`. -/
noncomputable def chebyshev_witt_completed_chebyshev_poly (d : ℕ) : Polynomial ℚ :=
  (completionTracePoly d).map (Int.castRingHom ℚ)

/-- In the seed completed model, the primitive Witt coordinate is the constant polynomial `1`. -/
noncomputable def chebyshev_witt_completed_primitive (_n : ℕ) : Polynomial ℚ :=
  Polynomial.C 1

/-- Scalar ghost coordinate obtained by summing the divisor weights `d`. -/
noncomputable def chebyshev_witt_completed_ghost_scalar (n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, (d : ℚ)

/-- The completed ghost polynomial attached to the divisor-sum model. -/
noncomputable def chebyshev_witt_completed_ghost (n : ℕ) : Polynomial ℚ :=
  Polynomial.C (chebyshev_witt_completed_ghost_scalar n)

private lemma chebyshev_witt_completed_mobius_scalar (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℚ) * chebyshev_witt_completed_ghost_scalar (n / d) =
      n := by
  have hsum :
      ∀ m : ℕ, 0 < m →
        Finset.sum (m.divisors) (fun i : ℕ => (i : ℚ)) =
          chebyshev_witt_completed_ghost_scalar m := by
    intro m hm
    simp [chebyshev_witt_completed_ghost_scalar]
  have hmobius :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun m => (m : ℚ))
      (g := chebyshev_witt_completed_ghost_scalar)).mp hsum
  have hanti := hmobius n hn
  rw [Nat.sum_divisorsAntidiagonal
      (f := fun d m =>
        (ArithmeticFunction.moebius d : ℚ) * chebyshev_witt_completed_ghost_scalar m)] at hanti
  simpa using hanti

/-- Paper label: `cor:chebyshev-witt-completed`. The completed primitive package descends the
power map `u ↦ u^d` to the Chebyshev action `s ↦ C_d(s)`, and in the concrete divisor-sum model
the completed ghost/primitive coordinates satisfy the two Witt inversion formulas. -/
theorem paper_chebyshev_witt_completed :
    (∀ d : ℕ, chebyshevTraceFormula d) ∧
      (∀ n : ℕ, 1 ≤ n →
        chebyshev_witt_completed_primitive n =
          Polynomial.C ((n : ℚ)⁻¹) *
            ∑ d ∈ n.divisors,
              Polynomial.C (ArithmeticFunction.moebius d : ℚ) *
                (chebyshev_witt_completed_ghost (n / d)).comp
                  (chebyshev_witt_completed_chebyshev_poly d)) ∧
      (∀ n : ℕ, 1 ≤ n →
        chebyshev_witt_completed_ghost n =
          ∑ d ∈ n.divisors,
            Polynomial.C (d : ℚ) *
              (chebyshev_witt_completed_primitive d).comp
                (chebyshev_witt_completed_chebyshev_poly (n / d))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    exact paper_primitive_completion_hatp.2.2 d
  · intro n hn
    have hnq : (n : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    have hscalar := chebyshev_witt_completed_mobius_scalar n hn
    have hnorm :
        (n : ℚ)⁻¹ *
            (∑ d ∈ n.divisors,
              (ArithmeticFunction.moebius d : ℚ) *
                chebyshev_witt_completed_ghost_scalar (n / d)) =
          1 := by
      rw [hscalar]
      field_simp [hnq]
    simpa [chebyshev_witt_completed_primitive, chebyshev_witt_completed_ghost,
      chebyshev_witt_completed_chebyshev_poly] using (congrArg Polynomial.C hnorm).symm
  · intro n hn
    simp [chebyshev_witt_completed_primitive, chebyshev_witt_completed_ghost,
      chebyshev_witt_completed_ghost_scalar, chebyshev_witt_completed_chebyshev_poly]

end Omega.SyncKernelWeighted
