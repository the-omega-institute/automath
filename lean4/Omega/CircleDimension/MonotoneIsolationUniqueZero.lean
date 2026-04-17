import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Monotone isolation unique-zero

The paper proof of `thm:cdim-monotone-isolation-unique-zero` invokes continuity of `Z'`,
strict monotonicity on a closed interval, the intermediate value theorem, and the mean value
theorem. The requested Lean signature does not include the continuity/differentiability
hypotheses needed to justify those steps, so this module is kept intentionally theorem-free and
the corresponding TeX label is marked partial rather than introducing a false theorem.
-/

namespace Omega.CircleDimension

end Omega.CircleDimension
