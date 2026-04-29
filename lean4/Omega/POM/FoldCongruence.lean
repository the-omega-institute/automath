import Omega.Folding.MaxFiberTwoStep

namespace Omega.POM

/-- lem:pom-fold-congruence -/
theorem paper_pom_fold_congruence {m : Nat} (w w' : Omega.Word m) :
    Omega.Fold w = Omega.Fold w' ↔
      Omega.weight w % Nat.fib (m + 2) = Omega.weight w' % Nat.fib (m + 2) := by
  simpa using Omega.Fold_eq_iff_weight_mod w w'

/-- prop:pom-fold-as-section -/
theorem paper_pom_fold_as_section {m : Nat} :
    ∃ s : Nat → Omega.X m,
      ∀ w : Omega.Word m, Omega.Fold w = s (Omega.weight w % Nat.fib (m + 2)) := by
  refine ⟨fun r => Omega.X.ofNat m (r % Nat.fib (m + 2)), ?_⟩
  intro w
  apply Omega.X.eq_of_stableValue_eq'
  rw [Omega.stableValue_Fold_mod, Omega.X.stableValue_ofNat_mod]
  exact (Nat.mod_eq_of_lt
    (Nat.mod_lt (Omega.weight w) (Omega.fib_succ_pos (m + 1)))).symm

end Omega.POM
