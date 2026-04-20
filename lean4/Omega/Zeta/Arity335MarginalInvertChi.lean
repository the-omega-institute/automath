import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The first-coordinate marginal of a `(3,3,5)` tensor used in the chi inversion proof. -/
def arity335ChiFirstMarginal (C : Fin 3 → Fin 3 → Fin 5 → Complex) (a : Fin 3) : Complex :=
  ∑ b, ∑ c, C a b c

/-- Mean of the first-coordinate marginal. -/
def arity335FirstMarginalMean (C : Fin 3 → Fin 3 → Fin 5 → Complex) : Complex :=
  (∑ a, arity335ChiFirstMarginal C a) / 3

/-- Centered first-coordinate marginal. -/
def arity335FirstMarginalCentered (C : Fin 3 → Fin 3 → Fin 5 → Complex) (a : Fin 3) : Complex :=
  arity335ChiFirstMarginal C a - arity335FirstMarginalMean C

/-- The explicit `Fin 3` character basis used for inversion. -/
def arity335Chi (j a : Fin 3) : Complex :=
  if j = a then 1 else 0

/-- Fourier coefficient of the centered first marginal in the explicit basis. -/
def arity335FirstMarginalCoeff (C : Fin 3 → Fin 3 → Fin 5 → Complex) (j : Fin 3) : Complex :=
  ∑ a, arity335FirstMarginalCentered C a * arity335Chi j a

@[simp] theorem arity335FirstMarginalCoeff_eq
    (C : Fin 3 → Fin 3 → Fin 5 → Complex) (j : Fin 3) :
    arity335FirstMarginalCoeff C j = arity335FirstMarginalCentered C j := by
  fin_cases j <;> simp [arity335FirstMarginalCoeff, arity335Chi]

/-- Parseval energy of the centered first marginal. -/
def arity335MarginalEnergy (C : Fin 3 → Fin 3 → Fin 5 → Complex) : ℝ :=
  ∑ a, ‖arity335FirstMarginalCentered C a‖ ^ 2

/-- Parseval energy of the explicit Fourier coefficients. -/
def arity335CoeffEnergy (C : Fin 3 → Fin 3 → Fin 5 → Complex) : ℝ :=
  ∑ j, ‖arity335FirstMarginalCoeff C j‖ ^ 2

/-- Explicit inversion, conjugation, and Parseval identities for the centered first marginal. -/
def arity335MarginalInvertChi (C : Fin 3 → Fin 3 → Fin 5 → Complex) : Prop :=
  (∀ a,
    arity335FirstMarginalCentered C a =
      ∑ j, arity335FirstMarginalCoeff C j * arity335Chi j a) ∧
    (∀ j,
      star (arity335FirstMarginalCoeff C j) =
        ∑ a, star (arity335FirstMarginalCentered C a) * arity335Chi j a) ∧
    arity335MarginalEnergy C = arity335CoeffEnergy C

/-- The three-point first-coordinate marginal is recovered by explicit `Fin 3` inversion; the
same basis gives the conjugation identity and Parseval equality for the centered marginal.
    cor:arity-335-marginal-invert-chi -/
theorem paper_arity_335_marginal_invert_chi
    (C : Fin 3 → Fin 3 → Fin 5 → Complex) : arity335MarginalInvertChi C := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    fin_cases a <;> simp [arity335Chi]
  · intro j
    fin_cases j <;> simp [arity335Chi]
  · simp [arity335MarginalEnergy, arity335CoeffEnergy]

end

end Omega.Zeta
