import Omega.Folding.MaxFiberTwoStep

namespace Omega.POM

/-- lem:pom-fold-congruence -/
theorem paper_pom_fold_congruence {m : Nat} (w w' : Omega.Word m) :
    Omega.Fold w = Omega.Fold w' ↔
      Omega.weight w % Nat.fib (m + 2) = Omega.weight w' % Nat.fib (m + 2) := by
  simpa using Omega.Fold_eq_iff_weight_mod w w'

end Omega.POM
