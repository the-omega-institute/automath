import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-gauge-constant-even-zeta-recovery`. -/
theorem paper_xi_foldbin_gauge_constant_even_zeta_recovery
    (recoveredBernoulli recoveredEvenZeta : ℕ -> Prop)
    (hbaseB : recoveredBernoulli 1)
    (hstepB :
      ∀ r, 2 ≤ r -> (∀ j, 1 ≤ j -> j < r -> recoveredBernoulli j) ->
        recoveredBernoulli r)
    (hzeta : ∀ r, 1 ≤ r -> recoveredBernoulli r -> recoveredEvenZeta r) :
    ∀ r, 1 ≤ r -> recoveredBernoulli r ∧ recoveredEvenZeta r := by
  have hBernoulli : ∀ r, 1 ≤ r -> recoveredBernoulli r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro hr
        by_cases hbase : r = 1
        · simpa [hbase] using hbaseB
        · have htwo : 2 ≤ r := by omega
          exact hstepB r htwo (by
            intro j hjpos hjlt
            exact ih j hjlt hjpos)
  intro r hr
  have hB : recoveredBernoulli r := hBernoulli r hr
  exact ⟨hB, hzeta r hr hB⟩

end Omega.Zeta
