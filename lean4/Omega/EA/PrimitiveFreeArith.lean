import Omega.EA.ArithComposition
import Omega.EA.FoldAsSectionCorollary
import Omega.EA.ZeckendorfTransversal
import Omega.Folding.Fiber

namespace Omega.EA

/-- Paper-facing corollary bundling the already formalized quotient, transversal, section, and
composition statements used to eliminate arithmetic primitives from the stable configuration
language.
    cor:primitive-free-arith -/
theorem paper_primitive_free_arith {A : Type _} (g : A → A) (m : Nat) :
    (Function.Bijective (Omega.X.stableValueFin (m := m))) ∧
      (∀ a : Omega.Rewrite.DigitCfg, Omega.EA.paper_zeckendorf_transversal_stmt a) ∧
      (∀ n : Fin (Nat.fib (m + 2)), ∃! x : Omega.X m, Omega.X.stableValueFin x = n) ∧
      Omega.EA.ArithComposition.paper_arith_composition g m := by
  refine ⟨Omega.X.stableValueFin_bijective m, ?_, ?_, ?_⟩
  · intro a
    exact Omega.EA.paper_zeckendorf_transversal a
  · exact Omega.EA.paper_zeckendorf_fold_as_section_seeds m
  · exact Omega.EA.ArithComposition.arithCompositionPackage g m

end Omega.EA
