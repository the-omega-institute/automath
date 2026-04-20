import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Omega.POM.MinkowskiBudgetBarrier

namespace Omega.POM

/-- The requested theorem signature for `prop:pom-multi-axis-near1-density` is false with the
current definitions: the left-hand side uses a natural power of `√s`, while the right-hand side
uses the real power `s^(d/2)` without the nonnegativity hypotheses that make the two expressions
agree. -/
theorem paper_pom_multi_axis_near1_density_signature_false :
    ¬ ∀ d : Nat, ∀ Vd detSigma B lam eps : Real,
      Omega.POM.pomEllipsoidVolume d Vd detSigma (Real.sqrt (2 * Real.log lam * eps)) /
          Omega.POM.pomLatticeDeterminant d B =
        (B / (2 * Real.pi) ^ d) * (Vd / Real.sqrt detSigma) *
          (2 * Real.log lam * eps) ^ ((d : Real) / 2) := by
  intro h
  have hbad := h 2 1 1 1 (Real.exp (-1)) (1 / 2)
  norm_num [Omega.POM.pomEllipsoidVolume, Omega.POM.pomLatticeDeterminant] at hbad

end Omega.POM
