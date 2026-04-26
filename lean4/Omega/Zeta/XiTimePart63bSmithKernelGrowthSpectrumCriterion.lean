import Omega.Zeta.SmithPrefixSufficiency

namespace Omega.Zeta

open scoped BigOperators

/-- Paper label: `thm:xi-time-part63b-smith-kernel-growth-spectrum-criterion`. -/
theorem paper_xi_time_part63b_smith_kernel_growth_spectrum_criterion {m : ℕ}
    (eA eB : Fin m → ℕ) :
    (∀ k : ℕ, Omega.Zeta.smithPrefixValue eA k = Omega.Zeta.smithPrefixValue eB k) ↔
      (∀ ℓ : ℕ,
        Omega.Zeta.smithPrefixMultiplicity eA ℓ =
          Omega.Zeta.smithPrefixMultiplicity eB ℓ) := by
  constructor
  · intro hValue ℓ
    have hDelta : ∀ k : ℕ, smithPrefixDelta eA k = smithPrefixDelta eB k := by
      intro k
      cases k with
      | zero =>
          simp [smithPrefixDelta]
      | succ k =>
          rw [smithPrefixDelta_eq_sub eA k, smithPrefixDelta_eq_sub eB k,
            hValue (k + 1), hValue k]
    rw [smithPrefixMultiplicity_eq_delta_sub_delta eA ℓ,
      smithPrefixMultiplicity_eq_delta_sub_delta eB ℓ, hDelta ℓ, hDelta (ℓ + 1)]
  · intro hMultiplicity k
    have hDelta_mono : ∀ (e : Fin m → ℕ) (k : ℕ),
        smithPrefixDelta e (k + 1) ≤ smithPrefixDelta e k := by
      intro e k
      unfold smithPrefixDelta
      refine Finset.sum_le_sum ?_
      intro i _
      by_cases hnext : k + 1 ≤ e i
      · have hcurr : k ≤ e i := le_trans (Nat.le_succ k) hnext
        simp [hcurr, hnext]
      · by_cases hcurr : k ≤ e i <;> simp [hcurr, hnext]
    have hDelta : ∀ k : ℕ, smithPrefixDelta eA k = smithPrefixDelta eB k := by
      intro k
      induction k with
      | zero =>
          simp [smithPrefixDelta]
      | succ k ih =>
          have hA := smithPrefixMultiplicity_eq_delta_sub_delta eA k
          have hB := smithPrefixMultiplicity_eq_delta_sub_delta eB k
          have hleA := hDelta_mono eA k
          have hleB := hDelta_mono eB k
          have hm := hMultiplicity k
          omega
    induction k with
    | zero =>
        simp [smithPrefixValue]
    | succ k ih =>
        rw [smithPrefix_succ_eq_add_delta eA k, smithPrefix_succ_eq_add_delta eB k,
          ih, hDelta (k + 1)]

end Omega.Zeta
