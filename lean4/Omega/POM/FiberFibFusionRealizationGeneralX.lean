import Omega.POM.FiberCategoricalSymmetryFibonacciFusion

namespace Omega.POM

/-- Paper label: `cor:pom-fiber-fib-fusion-realization-general-x`. -/
theorem paper_pom_fiber_fib_fusion_realization_general_x
    (components : List FiberFibonacciFusionData) :
    (∀ D, D ∈ components →
      Nonempty (D.independentSets ≃ D.fusionPathBasis) ∧
        D.fusionPathBasisCard = Nat.fib (D.ell + 2)) := by
  intro D _hD
  exact paper_pom_fiber_fibonacci_anyon_fusion_path_bijection D

end Omega.POM
