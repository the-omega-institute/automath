import Omega.Folding.BayesKinkGeometry
import Omega.Folding.GodelCoprimeInflation
import Omega.Folding.GodelFiniteDictionaryBitlength

namespace Omega.Folding

/-- Paper label: `cor:fold-gauge-anomaly-mismatch-primorial-growth`.
Specializing the coprime Gödel inflation theorem to the mismatch indicator `M` forces every active
prefix to dominate the matching primorial baseline, hence any single-integer coprime
externalization inherits the corresponding bitlength lower bound; in the prime-register
specialization the code is also bounded above by the full prefix primorial. -/
theorem paper_fold_gauge_anomaly_mismatch_primorial_growth
    (q : ℕ → ℕ) (M : ℕ → Bool) :
    (PairwiseCoprimeRegister q ∧ RegisterLowerBound q →
      ∀ m,
        Omega.POM.firstPrimeProduct (activeCount M m) ≤ prefixGodelProduct q M m ∧
          bitLength (Omega.POM.firstPrimeProduct (activeCount M m)) ≤
            bitLength (prefixGodelProduct q M m)) ∧
      (PrimeRegisterSpecialization q →
        ∀ m, prefixGodelProduct q M m ≤ Omega.POM.firstPrimeProduct m) := by
  let α : ℝ := (gStar (1 / 2 : ℚ) : ℝ)
  have hSpec := paper_fold_gauge_anomaly_godel_coprime_inflation q M α
  refine ⟨?_, hSpec.2⟩
  intro hq m
  have hLower := hSpec.1 hq m
  exact ⟨hLower, bitLength_mono hLower⟩

end Omega.Folding
