import Omega.Folding.S3Recurrence

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- Phase 162: CC shift identity + S_3 structural consequences
-- ══════════════════════════════════════════════════════════════

/-- ewc at level m+1 with shifted argument equals ewc at level m. -/
private theorem ewc_succ_shift (m n : Nat) (_hn : n < Nat.fib (m + 2)) :
    exactWeightCount (m + 1) (n + Nat.fib (m + 3)) =
    exactWeightCount m (n + Nat.fib (m + 1)) := by
  rw [exactWeightCount_succ]
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have hge : Nat.fib (m + 2) ≤ n + Nat.fib (m + 3) := by omega
  rw [if_pos hge]
  have hsub : n + Nat.fib (m + 3) - Nat.fib (m + 2) = n + Nat.fib (m + 1) := by omega
  rw [hsub, exactWeightCount_eq_zero_of_ge_fib m (n + Nat.fib (m + 3)) (by omega)]
  simp

/-- ewc at level m+1 equals ewc at level m for small arguments. -/
private theorem ewc_succ_small (m n : Nat) (hn : n < Nat.fib (m + 2)) :
    exactWeightCount (m + 1) n = exactWeightCount m n := by
  rw [exactWeightCount_succ]; simp [show ¬(Nat.fib (m + 2) ≤ n) from by omega]

/-- CCSH(m+1) = CCSH'(m).
    bridge:ccsh-succ-eq-prev -/
theorem crossCorrSqHigh_succ_eq_prev (m : Nat) :
    crossCorrSqHigh (m + 1) = crossCorrSqHighPrev m := by
  simp only [crossCorrSqHigh, crossCorrSqHighPrev]
  -- Both sums effectively only have nonzero terms for n < F_{m+2}.
  -- LHS: sum over n < F_{m+4}, but ewc_{m+1}(n+F_{m+3}) = 0 for n ≥ F_{m+2}.
  -- RHS: sum over n < F_{m+3}, but ewc_m(n+F_{m+1}) = 0 for n ≥ F_{m+2}.
  -- Convert both to sums over n < F_{m+2}.
  have hfib4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
  have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  -- LHS truncation
  have lhs_trunc : ∀ n, n ∈ Finset.range (Nat.fib (m + 4)) →
      n ∉ Finset.range (Nat.fib (m + 2)) →
      exactWeightCount (m + 1) n ^ 2 *
      exactWeightCount (m + 1) (n + Nat.fib ((m + 1) + 2)) = 0 := by
    intro n hn hn'
    simp only [Finset.mem_range] at hn hn'; push_neg at hn'
    have : Nat.fib (m + 4) ≤ n + Nat.fib (m + 3) := by omega
    rw [show (m + 1) + 2 = m + 3 from by omega,
        exactWeightCount_eq_zero_of_ge_fib (m + 1) _ this]; simp
  -- RHS truncation
  have rhs_trunc : ∀ n, n ∈ Finset.range (Nat.fib (m + 3)) →
      n ∉ Finset.range (Nat.fib (m + 2)) →
      exactWeightCount m n ^ 2 * exactWeightCount m (n + Nat.fib (m + 1)) = 0 := by
    intro n hn hn'
    simp only [Finset.mem_range] at hn hn'; push_neg at hn'
    have : Nat.fib (m + 3) ≤ n + Nat.fib (m + 1) := by omega
    rw [exactWeightCount_eq_zero_of_ge_fib m _ this]; simp
  conv_lhs => rw [show (m + 1) + 3 = m + 4 from by omega]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.fib_mono (by omega : m + 2 ≤ m + 4)))
        lhs_trunc,
      ← Finset.sum_subset (Finset.range_mono (Nat.fib_mono (by omega : m + 2 ≤ m + 3)))
        rhs_trunc]
  apply Finset.sum_congr rfl; intro n hn
  have hn' : n < Nat.fib (m + 2) := Finset.mem_range.mp hn
  rw [show (m + 1) + 2 = m + 3 from by omega,
      ewc_succ_small m n hn', ewc_succ_shift m n hn']

/-- CCSL(m+1) = CCSL'(m).
    bridge:ccsl-succ-eq-prev -/
theorem crossCorrSqLow_succ_eq_prev (m : Nat) :
    crossCorrSqLow (m + 1) = crossCorrSqLowPrev m := by
  simp only [crossCorrSqLow, crossCorrSqLowPrev]
  have hfib4 : Nat.fib (m + 4) = Nat.fib (m + 2) + Nat.fib (m + 3) := Nat.fib_add_two
  have hfib3 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have lhs_trunc : ∀ n, n ∈ Finset.range (Nat.fib (m + 4)) →
      n ∉ Finset.range (Nat.fib (m + 2)) →
      exactWeightCount (m + 1) n *
      exactWeightCount (m + 1) (n + Nat.fib ((m + 1) + 2)) ^ 2 = 0 := by
    intro n hn hn'
    simp only [Finset.mem_range] at hn hn'; push_neg at hn'
    have : Nat.fib (m + 4) ≤ n + Nat.fib (m + 3) := by omega
    rw [show (m + 1) + 2 = m + 3 from by omega,
        exactWeightCount_eq_zero_of_ge_fib (m + 1) _ this]; simp
  have rhs_trunc : ∀ n, n ∈ Finset.range (Nat.fib (m + 3)) →
      n ∉ Finset.range (Nat.fib (m + 2)) →
      exactWeightCount m n * exactWeightCount m (n + Nat.fib (m + 1)) ^ 2 = 0 := by
    intro n hn hn'
    simp only [Finset.mem_range] at hn hn'; push_neg at hn'
    have : Nat.fib (m + 3) ≤ n + Nat.fib (m + 1) := by omega
    rw [exactWeightCount_eq_zero_of_ge_fib m _ this]; simp
  conv_lhs => rw [show (m + 1) + 3 = m + 4 from by omega]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.fib_mono (by omega : m + 2 ≤ m + 4)))
        lhs_trunc,
      ← Finset.sum_subset (Finset.range_mono (Nat.fib_mono (by omega : m + 2 ≤ m + 3)))
        rhs_trunc]
  apply Finset.sum_congr rfl; intro n hn
  have hn' : n < Nat.fib (m + 2) := Finset.mem_range.mp hn
  rw [show (m + 1) + 2 = m + 3 from by omega,
      ewc_succ_small m n hn', ewc_succ_shift m n hn']

/-- CCSH(m+1) + CCSL(m+1) = CCSH'(m) + CCSL'(m).
    bridge:cc-succ-ccs-prime -/
theorem cc_succ_eq_ccs_prime (m : Nat) :
    crossCorrSqHigh (m + 1) + crossCorrSqLow (m + 1) =
    crossCorrSqHighPrev m + crossCorrSqLowPrev m := by
  rw [crossCorrSqHigh_succ_eq_prev, crossCorrSqLow_succ_eq_prev]

/-- S_3(m+1) + EWT(m+1) = EWT(m+2).
    prop:pom-s3-recurrence -/
theorem momentSum_three_add_ewt (m : Nat) :
    momentSum 3 (m + 1) + exactWeightTriple (m + 1) = exactWeightTriple (m + 2) := by
  have h1 := momentSum_three_eq_ewt_plus_ccs m
  have hcc := cc_succ_eq_ccs_prime m
  have h2 := exactWeightTriple_succ (m + 1)
  -- h1: S(m+1) = E(m+1) + 3·CCSH'(m) + 3·CCSL'(m)
  -- hcc: CCSH(m+1)+CCSL(m+1) = CCSH'(m)+CCSL'(m)
  -- h2: E(m+1+1) = 2E(m+1) + 3·CCSH(m+1) + 3·CCSL(m+1)
  -- Need: S(m+1) + E(m+1) = E(m+2)
  -- S(m+1) = E(m+1) + 3(CCSH'(m)+CCSL'(m)) = E(m+1) + 3(CCSH(m+1)+CCSL(m+1))
  -- E(m+2) = 2E(m+1) + 3(CCSH(m+1)+CCSL(m+1))
  -- → S(m+1) + E(m+1) = 2E(m+1) + 3(CCSH(m+1)+CCSL(m+1)) = E(m+2) ✓
  -- The issue: h2 has E(m+1+1) not E(m+2). They're definitionally equal.
  show momentSum 3 (m + 1) + exactWeightTriple (m + 1) = exactWeightTriple (m + 2)
  linarith

end Omega
