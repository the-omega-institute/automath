import Mathlib.Tactic
import Omega.Conclusion.PoissonCauchyTracelessQuadrupoleFactorization

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-poisson-cauchy-exact-124-pythagoras`. The two projected
constants agree, their sum is the raw constant, and the Fisher constant is exactly four times the
raw one. -/
theorem paper_conclusion_poisson_cauchy_exact_124_pythagoras {A B raw proj bridge fisher : ℝ}
    (hRaw : raw = A ^ 2 / 8 + B ^ 2 / 2) (hProj : proj = A ^ 2 / 16 + B ^ 2 / 4)
    (hBridge : bridge = A ^ 2 / 16 + B ^ 2 / 4) (hFisher : fisher = A ^ 2 / 2 + 2 * B ^ 2) :
    raw = proj + bridge ∧ raw = 2 * proj ∧ fisher = 4 * raw := by
  subst raw
  subst proj
  subst bridge
  subst fisher
  constructor
  · ring
  constructor
  · ring
  · ring

end Omega.Conclusion
