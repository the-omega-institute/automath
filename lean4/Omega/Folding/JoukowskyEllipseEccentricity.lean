import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Folding.FibKernelBasisFiniteDepth

namespace Omega.Folding

/-- Paper-facing Joukowsky ellipse wrapper: the standard trigonometric parametrization satisfies
the ellipse equation, the eccentricity has the closed form `2 * sqrt t / (1 + t)`, the same
quantity is the hyperbolic secant of the logarithmic radius, and the finite-depth residual kernel
package from `paper_fib_kernel_basis_finite_depth` is available uniformly in `L`.
    thm:joukowsky-ellipse-eccentricity -/
theorem paper_joukowsky_ellipse_eccentricity (t : Real) (ht : 0 < t) :
    (∀ θ : Real, t ≠ 1 →
      let x := (1 + t) * Real.cos θ
      let y := (1 - t) * Real.sin θ
      (x / (1 + t)) ^ 2 + (y / (1 - t)) ^ 2 = 1) ∧
    Real.sqrt (1 - (|1 - t| / (1 + t)) ^ 2) = 2 * Real.sqrt t / (1 + t) ∧
    2 * Real.sqrt t / (1 + t) = 1 / Real.cosh (Real.log (Real.sqrt t)) ∧
    (∀ L : ℕ,
      (∀ k, k < L → Omega.EA.ledgerValZ (Omega.EA.residualBasisGenerator k) = 0) ∧
      (∀ k, k < L → ∀ j, k + 2 < j → Omega.EA.residualBasisGenerator k j = 0) ∧
      Function.Injective Omega.EA.Theta ∧
      (∀ a b : Omega.EA.DigitCfg, Omega.EA.NF_pr a = Omega.EA.NF_pr b →
        Omega.EA.R a = Omega.EA.R b → a = b)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro θ ht1
    dsimp
    have htp : (1 + t : Real) ≠ 0 := by linarith
    have htm : (1 - t : Real) ≠ 0 := sub_ne_zero.mpr ht1.symm
    have hx : ((1 + t) * Real.cos θ / (1 + t) : Real) = Real.cos θ := by
      field_simp [htp]
    have hy : ((1 - t) * Real.sin θ / (1 - t) : Real) = Real.sin θ := by
      field_simp [htm]
    rw [hx, hy]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · have htp : (1 + t : Real) ≠ 0 := by linarith
    have hsq :
        1 - (|1 - t| / (1 + t)) ^ 2 = (2 * Real.sqrt t / (1 + t)) ^ 2 := by
      have habs : |1 - t| ^ 2 = (1 - t) ^ 2 := by rw [sq_abs]
      field_simp [htp]
      rw [habs, Real.sq_sqrt ht.le]
      ring
    have hnonneg : 0 ≤ 2 * Real.sqrt t / (1 + t) := by positivity
    calc
      Real.sqrt (1 - (|1 - t| / (1 + t)) ^ 2)
          = Real.sqrt ((2 * Real.sqrt t / (1 + t)) ^ 2) := by rw [hsq]
      _ = |2 * Real.sqrt t / (1 + t)| := by rw [Real.sqrt_sq_eq_abs]
      _ = 2 * Real.sqrt t / (1 + t) := abs_of_nonneg hnonneg
  · have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    have hsqrt_ne : (Real.sqrt t : Real) ≠ 0 := ne_of_gt hsqrt_pos
    rw [Real.cosh_log hsqrt_pos]
    field_simp [hsqrt_ne]
    nlinarith [Real.sq_sqrt ht.le]
  · intro L
    exact paper_fib_kernel_basis_finite_depth L

end Omega.Folding
