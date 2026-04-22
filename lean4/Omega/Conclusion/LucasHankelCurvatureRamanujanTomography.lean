import Mathlib.Tactic
import Omega.Conclusion.LucasNormalizedHankelDiscreteCurvature
import Omega.Conclusion.SmithPrimepowerHessianInversion
import Omega.Conclusion.SmithRamanujanShadowSeeds

namespace Omega.Conclusion

open Omega.Zeta.LucasBarrier

/-- Coefficient extracted from the second differences of the discrete loss profile. -/
def conclusion_lucas_hankel_curvature_ramanujan_tomography_second_difference_coeff
    {α : Type*} [Fintype α] [DecidableEq α] (valuation : α → ℕ) (k : ℕ) : ℕ :=
  2 * lossProfile valuation k - lossProfile valuation (k - 1) - lossProfile valuation (k + 1)

/-- Paper label: `thm:conclusion-lucas-hankel-curvature-ramanujan-tomography`.
The normalized Lucas Hankel minors satisfy the discrete-curvature recursion already formalized in
the chapter. On the divisor side, the second differences of the finite loss profile recover the
exact layer multiplicities, and the classical Ramanujan shadow identity packages the coefficient
formula for the resulting tomography. -/
theorem paper_conclusion_lucas_hankel_curvature_ramanujan_tomography
    {α : Type*} [Fintype α] [DecidableEq α] (valuation : α → ℕ) :
    (∀ n k : ℕ,
      lucas (n + 1) * lucasNormalizedHankelMinor (n + 1) k =
        lucasNormalizedHankelMinor n (k + 1)) ∧
      (∀ k : ℕ, 1 ≤ k →
        conclusion_lucas_hankel_curvature_ramanujan_tomography_second_difference_coeff
            valuation k =
          layerMultiplicity valuation k) ∧
      (∀ (p : ℤ) (k : ℕ) (_hk : 0 < k),
        p ^ (k - 1) * (p - 1) * (tailCount valuation k : ℤ) +
            (-(p ^ (k - 1))) *
              ((tailCount valuation (k - 1) : ℤ) - (tailCount valuation k : ℤ)) =
          p ^ k * (tailCount valuation k : ℤ) -
            p ^ (k - 1) * (tailCount valuation (k - 1) : ℤ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n k
    exact (paper_conclusion_lucas_normalized_hankel_discrete_curvature n k).2.2
  · intro k hk
    simpa [conclusion_lucas_hankel_curvature_ramanujan_tomography_second_difference_coeff] using
      (paper_conclusion_smith_primepower_hessian_inversion valuation k hk).symm
  · intro p k _hk
    exact (paper_conclusion_smith_ramanujan_shadow_formula).1 p k (by omega)
      (tailCount valuation (k - 1) : ℤ) (tailCount valuation k : ℤ)

end Omega.Conclusion
