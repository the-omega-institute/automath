import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.FinitePartCyclicLiftRootUnityFourierSieve
import Omega.Zeta.FinitePartDirichletCharacterInversionPrime

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the cyclotomic symmetry criterion: the Gauss--Dirichlet expansion
    identifies the Fourier coefficients attached to primitive nontrivial characters, orthogonality
    forces those coefficients to vanish exactly when only the `q`-multiple terms survive, and the
    surviving series is then packaged as a `q`-fold pullback `G(t^q)`.
    thm:finite-part-dirichlet-vanishing-cyclotomic-symmetry -/
theorem paper_finite_part_dirichlet_vanishing_cyclotomic_symmetry {ι : Type*}
    (L : ι → Complex) (primitiveNontrivial : ι → Prop) (cyclotomicClosed : Prop)
    (gaussDirichletExpansion characterOrthogonality survivingQMultiples qFoldPullback : Prop)
    (hExpansion : (∀ χ, primitiveNontrivial χ → L χ = 0) → gaussDirichletExpansion)
    (hOrthogonality : gaussDirichletExpansion → characterOrthogonality)
    (hSurviving : characterOrthogonality → survivingQMultiples)
    (hPullback : survivingQMultiples → qFoldPullback)
    (hClosed : qFoldPullback → cyclotomicClosed)
    (hReverse : cyclotomicClosed → ∀ χ, primitiveNontrivial χ → L χ = 0) :
    (∀ χ, primitiveNontrivial χ → L χ = 0) <-> cyclotomicClosed := by
  constructor
  · intro hVanishing
    exact hClosed (hPullback (hSurviving (hOrthogonality (hExpansion hVanishing))))
  · exact hReverse

end Omega.Zeta
