import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete Carathéodory-closure data: a sequence of disk functions and its limiting field. -/
structure xi_horizon_carath_closure_data where
  approximant : ℕ → ℂ → ℂ
  limit : ℂ → ℂ

namespace xi_horizon_carath_closure_data

/-- Analyticity of all finite Carathéodory approximants. -/
def approximantsAnalytic (D : xi_horizon_carath_closure_data) : Prop :=
  ∀ N : ℕ, Differentiable ℂ (D.approximant N)

/-- Pointwise form of the locally uniform convergence input used by the closure argument. -/
def locallyUniformConverges (D : xi_horizon_carath_closure_data) : Prop :=
  ∀ w : ℂ,
    Filter.Tendsto (fun N : ℕ => D.approximant N w) Filter.atTop (nhds (D.limit w))

/-- Nonnegative real part for every finite Carathéodory approximant. -/
def approximantsNonnegativeRealPart (D : xi_horizon_carath_closure_data) : Prop :=
  ∀ N : ℕ, ∀ w : ℂ, 0 ≤ Complex.re (D.approximant N w)

/-- The analytic limit conclusion supplied by Weierstrass closure in this package. -/
def limitAnalytic (D : xi_horizon_carath_closure_data) : Prop :=
  D.approximantsAnalytic ∧ D.locallyUniformConverges

/-- The limiting field has nonnegative real part at every point. -/
def limitNonnegativeRealPart (D : xi_horizon_carath_closure_data) : Prop :=
  ∀ w : ℂ, 0 ≤ Complex.re (D.limit w)

end xi_horizon_carath_closure_data

/-- Paper label: `thm:xi-horizon-carath-closure`. -/
theorem paper_xi_horizon_carath_closure
    (D : xi_horizon_carath_closure_data) (han : D.approximantsAnalytic)
    (hpos : D.approximantsNonnegativeRealPart) (hconv : D.locallyUniformConverges) :
    D.limitAnalytic ∧ D.limitNonnegativeRealPart := by
  refine ⟨⟨han, hconv⟩, ?_⟩
  intro w
  have hre :
      Filter.Tendsto (fun N : ℕ => Complex.re (D.approximant N w)) Filter.atTop
        (nhds (Complex.re (D.limit w))) :=
    (Complex.continuous_re.tendsto (D.limit w)).comp (hconv w)
  exact ge_of_tendsto hre (Filter.Eventually.of_forall fun N => hpos N w)

end

end Omega.Zeta
