import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Folding.FibonacciPolynomial
import Omega.UnitCirclePhaseArithmetic.FibUnitCircleUpliftIdentity

namespace Omega

open Omega.UnitCirclePhaseArithmetic

/-- Cyclotomic Lee--Yang root package for the path independent-set polynomial: every nontrivial
`(ℓ + 2)`-nd root of unity maps through the Lee--Yang coordinate to a zero of `pathIndSetPoly ℓ`.
-/
def PathIndSetLeyangCyclotomicRoots (ℓ : ℕ) : Prop :=
  ∀ u : ℂ, u ≠ 1 → u ≠ -1 → u ^ (ℓ + 2) = 1 →
    (((pathIndSetPoly ℓ).map (Int.castRingHom ℂ)).eval (leyangJ u) = 0)

/-- Paper label: `thm:pom-path-indset-leyang-cyclotomic-param`.
The path independent-set polynomial is the shifted Fibonacci polynomial by definition, and the
Lee--Yang cyclotomic parametrization follows from the unit-circle uplift identity specialized to an
`(ℓ + 2)`-nd root of unity. -/
theorem paper_pom_path_indset_leyang_cyclotomic_param (ℓ : ℕ) :
    pathIndSetPoly ℓ = fibPoly (ℓ + 2) ∧ PathIndSetLeyangCyclotomicRoots ℓ := by
  refine ⟨rfl, ?_⟩
  intro u hu1 hum1 hu
  have huplift :=
    paper_fib_unit_circle_uplift_identity (n := ℓ + 2) (by omega) u hu1 hum1
  have hgeom : (u ^ (ℓ + 2) - 1) / (u - 1) = 0 := by
    simp [hu]
  have hscaled :
      (1 + u) ^ (ℓ + 1) *
          (((pathIndSetPoly ℓ).map (Int.castRingHom ℂ)).eval (leyangJ u)) = 0 := by
    have hscaled' :
        (1 + u) ^ (ℓ + 2 - 1) * (fibPolyC (ℓ + 2)).eval (leyangJ u) = 0 :=
      huplift.trans hgeom
    simpa [pathIndSetPoly, fibPolyC] using hscaled'
  have hfac : (1 + u) ^ (ℓ + 1) ≠ 0 := by
    have hne : 1 + u ≠ 0 := by
      intro h
      exact hum1 (eq_neg_of_add_eq_zero_right h)
    exact pow_ne_zero (ℓ + 1) hne
  exact (mul_eq_zero.mp hscaled).resolve_left hfac

end Omega
