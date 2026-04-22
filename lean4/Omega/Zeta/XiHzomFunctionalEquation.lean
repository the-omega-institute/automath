import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped ComplexConjugate

/-- Concrete HZOM data: a Fredholm determinant model together with the horizon involution and the
two algebraic identities used in the reflection argument. -/
structure xi_hzom_functional_equation_data where
  determinant : ℂ → ℂ
  horizonInvolution : ℂ → ℂ
  detailedBalanceConjugacy :
    ∀ s, determinant (horizonInvolution s) = conj (determinant s)
  similarityInvariance :
    ∀ s, determinant (horizonInvolution (horizonInvolution s)) = determinant s

namespace xi_hzom_functional_equation_data

/-- The determinant satisfies the expected reflection identity across the horizon involution. -/
def determinant_reflection_symmetry (D : xi_hzom_functional_equation_data) : Prop :=
  ∀ s, D.determinant (D.horizonInvolution s) = conj (D.determinant s)

end xi_hzom_functional_equation_data

lemma xi_hzom_functional_equation_double_reflection
    (D : xi_hzom_functional_equation_data) (s : ℂ) :
    conj (D.determinant (D.horizonInvolution s)) = D.determinant s := by
  calc
    conj (D.determinant (D.horizonInvolution s))
        = conj (conj (D.determinant s)) := by
            rw [D.detailedBalanceConjugacy s]
    _ = D.determinant s := by simp

/-- Paper label: `prop:xi-hzom-functional-equation`. Detailed-balance conjugacy identifies the
horizon-reflected determinant with the complex conjugate determinant, and the similarity invariance
ensures this reflection is involutive on the Fredholm data. -/
theorem paper_xi_hzom_functional_equation
    (D : xi_hzom_functional_equation_data) : D.determinant_reflection_symmetry := by
  intro s
  exact D.detailedBalanceConjugacy s

end Omega.Zeta
