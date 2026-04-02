import Omega.Folding.EWTTelescope

namespace Omega

-- ══════════════════════════════════════════════════════════════
-- Phase 152-153: S_3 recurrence definitions + verification
-- ══════════════════════════════════════════════════════════════

/-- Cross-correlation-squared high at previous shift F_{m+1}: Σ ewc(n)² · ewc(n + F_{m+1}).
    bridge:ccsh-prev -/
def crossCorrSqHighPrev (m : Nat) : Nat :=
  ∑ n ∈ Finset.range (Nat.fib (m + 3)),
    exactWeightCount m n ^ 2 * exactWeightCount m (n + Nat.fib (m + 1))

/-- Cross-correlation-squared low at previous shift F_{m+1}: Σ ewc(n) · ewc(n + F_{m+1})².
    bridge:ccsl-prev -/
def crossCorrSqLowPrev (m : Nat) : Nat :=
  ∑ n ∈ Finset.range (Nat.fib (m + 3)),
    exactWeightCount m n * exactWeightCount m (n + Nat.fib (m + 1)) ^ 2

/-- tripleCollisionClass(fff) = exactTripleCollisionClass(fff).
    bridge:s3-fff-exact -/
theorem tripleCollisionClass_fff_eq_exact (m : Nat) :
    (tripleCollisionClass m false false false).card =
    (exactTripleCollisionClass m false false false).card := by
  congr 1; ext ⟨v1, v2, v3⟩
  simp only [tripleCollisionClass, exactTripleCollisionClass, Finset.mem_filter,
    Finset.mem_univ, true_and, Bool.false_eq_true, ite_false, Nat.add_zero]
  constructor
  · intro ⟨h1, h2⟩
    rw [Nat.mod_eq_of_lt (X.weight_lt_fib v1), Nat.mod_eq_of_lt (X.weight_lt_fib v2)] at h1
    rw [Nat.mod_eq_of_lt (X.weight_lt_fib v2), Nat.mod_eq_of_lt (X.weight_lt_fib v3)] at h2
    exact ⟨h1, h2⟩
  · intro ⟨h1, h2⟩
    constructor <;> (rw [Nat.mod_eq_of_lt (X.weight_lt_fib _), Nat.mod_eq_of_lt (X.weight_lt_fib _)])
    · exact h1
    · exact h2

/-- tripleCollisionClass(ttt) = exactTripleCollisionClass(ttt).
    bridge:s3-ttt-exact -/
theorem tripleCollisionClass_ttt_eq_exact (m : Nat) :
    (tripleCollisionClass m true true true).card =
    (exactTripleCollisionClass m true true true).card := by
  congr 1; ext ⟨v1, v2, v3⟩
  simp only [tripleCollisionClass, exactTripleCollisionClass, Finset.mem_filter,
    Finset.mem_univ, true_and, ite_true]
  constructor
  · intro ⟨h1, h2⟩
    have hmod1 : weight v1 % Nat.fib (m + 3) = weight v2 % Nat.fib (m + 3) :=
      Nat.ModEq.add_right_cancel' (Nat.fib (m + 2)) h1
    have hmod2 : weight v2 % Nat.fib (m + 3) = weight v3 % Nat.fib (m + 3) :=
      Nat.ModEq.add_right_cancel' (Nat.fib (m + 2)) h2
    rw [Nat.mod_eq_of_lt (X.weight_lt_fib v1), Nat.mod_eq_of_lt (X.weight_lt_fib v2)] at hmod1
    rw [Nat.mod_eq_of_lt (X.weight_lt_fib v2), Nat.mod_eq_of_lt (X.weight_lt_fib v3)] at hmod2
    exact ⟨by omega, by omega⟩
  · intro ⟨h1, h2⟩
    -- exact → mod: wt(v1)+F = wt(v2)+F → (wt(v1)+F)%F' = (wt(v2)+F)%F'
    refine ⟨?_, ?_⟩ <;> show _ % _ = _ % _ <;> congr 1

-- ══════════════════════════════════════════════════════════════
-- Phase 155: T_fft mod split via weight-class summation
-- ══════════════════════════════════════════════════════════════

/-- Count of words whose weight + F_{m+2} ≡ n (mod F_{m+3}).
    bridge:modular-weight-count -/
theorem modular_weight_count (m n : Nat) (hn : n < Nat.fib (m + 3)) :
    (Finset.univ.filter (fun v : Word m =>
      (weight v + Nat.fib (m + 2)) % Nat.fib (m + 3) = n)).card =
    if Nat.fib (m + 2) ≤ n then exactWeightCount m (n - Nat.fib (m + 2))
    else exactWeightCount m (n + Nat.fib (m + 1)) := by
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  split_ifs with hge
  · -- n ≥ F_{m+2}: (wt + F_{m+2}) % F_{m+3} = n ↔ wt = n - F_{m+2}
    -- Since n - F_{m+2} < F_{m+1} < F_{m+3}, wt + F_{m+2} = n < F_{m+3}, so mod is identity
    simp only [exactWeightCount]; congr 1; ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hvlt : weight v < Nat.fib (m + 3) := X.weight_lt_fib v
      have : weight v + Nat.fib (m + 2) < 2 * Nat.fib (m + 3) := by omega
      by_cases hlt : weight v + Nat.fib (m + 2) < Nat.fib (m + 3)
      · rw [Nat.mod_eq_of_lt hlt] at h; omega
      · push_neg at hlt
        rw [Nat.mod_eq_sub_mod hlt, Nat.mod_eq_of_lt (by omega)] at h; omega
    · intro h
      rw [h, Nat.sub_add_cancel hge, Nat.mod_eq_of_lt hn]
  · -- n < F_{m+2}: (wt + F_{m+2}) % F_{m+3} = n ↔ wt = n + F_{m+1}
    -- Since wt + F_{m+2} = n + F_{m+1} + F_{m+2} = n + F_{m+3} ≥ F_{m+3}, mod subtracts F_{m+3}
    push_neg at hge
    simp only [exactWeightCount]; congr 1; ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have hvlt : weight v < Nat.fib (m + 3) := X.weight_lt_fib v
      by_cases hlt : weight v + Nat.fib (m + 2) < Nat.fib (m + 3)
      · rw [Nat.mod_eq_of_lt hlt] at h; omega
      · push_neg at hlt
        rw [Nat.mod_eq_sub_mod hlt, Nat.mod_eq_of_lt (by omega)] at h; omega
    · intro h
      rw [h, show n + Nat.fib (m + 1) + Nat.fib (m + 2) = n + Nat.fib (m + 3) from by omega,
          Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hn]

set_option maxHeartbeats 800000 in
/-- T_{fft}(mod) expressed as sum over weight classes.
    bridge:fft-eq-sum -/
theorem tripleCollisionClass_fft_eq_sum (m : Nat) :
    (tripleCollisionClass m false false true).card =
    ∑ n ∈ Finset.range (Nat.fib (m + 3)),
      exactWeightCount m n ^ 2 *
      (Finset.univ.filter (fun v : Word m =>
        (weight v + Nat.fib (m + 2)) % Nat.fib (m + 3) = n)).card := by
  classical
  -- T_{fft}: wt(v1) % F = wt(v2) % F ∧ wt(v2) % F = (wt(v3)+F_{m+2}) % F
  -- Since wt < F, first condition is wt(v1) = wt(v2)
  -- Group by n = wt(v1) = wt(v2)
  simp only [tripleCollisionClass, exactWeightCount, Bool.false_eq_true, ite_false, ite_true,
    Nat.add_zero]
  -- Rewrite as product decomposition
  simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card ^ 2 *
    (Finset.univ.filter (fun v : Word m =>
      (weight v + Nat.fib (m + 2)) % Nat.fib (m + 3) = n)).card =
    ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
     ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
      (Finset.univ.filter (fun v : Word m =>
        (weight v + Nat.fib (m + 2)) % Nat.fib (m + 3) = n)))).card from
    fun n => by simp [Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2, v3⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro ⟨h1, h2⟩
      rw [Nat.mod_eq_of_lt (X.weight_lt_fib v1),
          Nat.mod_eq_of_lt (X.weight_lt_fib v2)] at h1
      rw [Nat.mod_eq_of_lt (X.weight_lt_fib v2)] at h2
      rw [← h1] at h2
      exact ⟨weight v1, X.weight_lt_fib v1, rfl, h1.symm, h2.symm⟩
    · rintro ⟨n, hn, hw1, hw2, hw3⟩
      have hv1 : weight v1 = n := hw1
      have hv2 : weight v2 = n := by omega
      refine ⟨?_, ?_⟩
      · show _ % _ = _ % _; rw [hv1, hv2]
      · show _ % _ = _ % _; rw [hv2, Nat.mod_eq_of_lt hn, ← hw3]
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨v1, _, _⟩ ⟨hw1, _⟩ ⟨hw1', _⟩
    exact hne (hw1.symm.trans hw1')

-- ewc vanishes for weights ≥ F_{m+3}
/-- bridge:ewc-zero-of-ge -/
private theorem ewc_zero_of_ge (m n : Nat) (hn : Nat.fib (m + 3) ≤ n) :
    exactWeightCount m n = 0 := by
  simp only [exactWeightCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _; exact Nat.ne_of_lt (by linarith [X.weight_lt_fib w])

/-- CCSL range truncates to F_{m+1}: for k ≥ F_{m+1}, ewc(k+F_{m+2}) = 0.
    bridge:ccsl-range-truncate -/
theorem crossCorrSqLow_range_truncate (m : Nat) :
    crossCorrSqLow m = ∑ k ∈ Finset.range (Nat.fib (m + 1)),
      exactWeightCount m k * exactWeightCount m (k + Nat.fib (m + 2)) ^ 2 := by
  unfold crossCorrSqLow
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  symm; apply Finset.sum_subset (Finset.range_mono (Nat.fib_mono (show m + 1 ≤ m + 3 by omega)))
  intro k hk hk'
  simp only [Finset.mem_range] at hk hk'; push_neg at hk'
  have : Nat.fib (m + 3) ≤ k + Nat.fib (m + 2) := by linarith [hfib]
  rw [ewc_zero_of_ge m _ this]; simp

/-- CCSH' range truncates to F_{m+2}: for n ≥ F_{m+2}, ewc(n+F_{m+1}) = 0.
    bridge:ccsh-prev-truncate -/
theorem crossCorrSqHighPrev_range_truncate (m : Nat) :
    crossCorrSqHighPrev m = ∑ n ∈ Finset.range (Nat.fib (m + 2)),
      exactWeightCount m n ^ 2 * exactWeightCount m (n + Nat.fib (m + 1)) := by
  unfold crossCorrSqHighPrev
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  symm; apply Finset.sum_subset (Finset.range_mono (Nat.fib_mono (show m + 2 ≤ m + 3 by omega)))
  intro n hn hn'
  simp only [Finset.mem_range] at hn hn'; push_neg at hn'
  have : Nat.fib (m + 3) ≤ n + Nat.fib (m + 1) := by linarith [hfib]
  rw [ewc_zero_of_ge m _ this]; simp

set_option maxHeartbeats 800000 in
/-- T_{fft}(mod) = CCSL + CCSH' (general, all m).
    prop:pom-s3-recurrence -/
theorem tripleCollisionClass_fft_mod_split (m : Nat) :
    (tripleCollisionClass m false false true).card =
    crossCorrSqLow m + crossCorrSqHighPrev m := by
  rw [tripleCollisionClass_fft_eq_sum]
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  -- Substitute modular_weight_count
  have hsubst : ∀ n ∈ Finset.range (Nat.fib (m + 3)),
      exactWeightCount m n ^ 2 *
      (Finset.univ.filter (fun v : Word m =>
        (weight v + Nat.fib (m + 2)) % Nat.fib (m + 3) = n)).card =
      if Nat.fib (m + 2) ≤ n
      then exactWeightCount m n ^ 2 * exactWeightCount m (n - Nat.fib (m + 2))
      else exactWeightCount m n ^ 2 * exactWeightCount m (n + Nat.fib (m + 1)) := by
    intro n hn; rw [modular_weight_count m n (Finset.mem_range.mp hn)]; split_ifs <;> rfl
  rw [Finset.sum_congr rfl hsubst, Finset.sum_ite]
  -- Goal: Σ_{n≥F₂} ewc(n)²·ewc(n-F₂) + Σ_{n<F₂} ewc(n)²·ewc(n+F₁) = CCSL + CCSH'
  congr 1
  · -- Σ_{n∈range(F₃), n≥F₂} ewc(n)²·ewc(n-F₂) = CCSL
    rw [crossCorrSqLow_range_truncate]
    -- Bijection: filter(range(F₃), ≥F₂) ↔ range(F₁) via n ↦ n - F₂
    apply Finset.sum_bij (fun n _ => n - Nat.fib (m + 2))
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      exact Finset.mem_range.mpr (by omega)
    · intro n1 hn1 n2 hn2 h
      simp only [Finset.mem_filter] at hn1 hn2; omega
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      exact ⟨k + Nat.fib (m + 2),
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩,
        by simp⟩
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      rw [Nat.sub_add_cancel hn.2]; ring
  · -- Σ_{n∈range(F₃), ¬(n≥F₂)} ewc(n)²·ewc(n+F₁) = CCSH'
    rw [crossCorrSqHighPrev_range_truncate]
    -- filter(range(F₃), ¬≥F₂) = range(F₂) (since F₂ ≤ F₃)
    congr 1
    ext n; simp only [Finset.mem_filter, Finset.mem_range, not_le]; omega

/-- CCSH range truncates to F_{m+1}.
    bridge:ccsh-range-truncate -/
theorem crossCorrSqHigh_range_truncate (m : Nat) :
    crossCorrSqHigh m = ∑ k ∈ Finset.range (Nat.fib (m + 1)),
      exactWeightCount m k ^ 2 * exactWeightCount m (k + Nat.fib (m + 2)) := by
  unfold crossCorrSqHigh
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  symm; apply Finset.sum_subset (Finset.range_mono (Nat.fib_mono (show m + 1 ≤ m + 3 by omega)))
  intro k hk hk'
  simp only [Finset.mem_range] at hk hk'; push_neg at hk'
  have : Nat.fib (m + 3) ≤ k + Nat.fib (m + 2) := by linarith
  rw [ewc_zero_of_ge m _ this]; simp

/-- CCSL' range truncates to F_{m+2}.
    bridge:ccsl-prev-truncate -/
theorem crossCorrSqLowPrev_range_truncate (m : Nat) :
    crossCorrSqLowPrev m = ∑ n ∈ Finset.range (Nat.fib (m + 2)),
      exactWeightCount m n * exactWeightCount m (n + Nat.fib (m + 1)) ^ 2 := by
  unfold crossCorrSqLowPrev
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  symm; apply Finset.sum_subset (Finset.range_mono (Nat.fib_mono (show m + 2 ≤ m + 3 by omega)))
  intro n hn hn'
  simp only [Finset.mem_range] at hn hn'; push_neg at hn'
  have : Nat.fib (m + 3) ≤ n + Nat.fib (m + 1) := by linarith
  rw [ewc_zero_of_ge m _ this]; simp

set_option maxHeartbeats 800000 in
/-- T_{ftt}(mod) expressed as sum over weight classes.
    Group by n = wt(v2) = wt(v3): v1 satisfies wt(v1) = (n+F₂)%F.
    bridge:ftt-eq-sum -/
theorem tripleCollisionClass_ftt_eq_sum (m : Nat) :
    (tripleCollisionClass m false true true).card =
    ∑ n ∈ Finset.range (Nat.fib (m + 3)),
      exactWeightCount m ((n + Nat.fib (m + 2)) % Nat.fib (m + 3)) *
      exactWeightCount m n ^ 2 := by
  classical
  simp only [tripleCollisionClass, exactWeightCount, Bool.false_eq_true, ite_false, ite_true,
    Nat.add_zero]
  simp_rw [show ∀ n,
    (Finset.univ.filter (fun w : Word m =>
      weight w = (n + Nat.fib (m + 2)) % Nat.fib (m + 3))).card *
    (Finset.univ.filter (fun w : Word m => weight w = n)).card ^ 2 =
    ((Finset.univ.filter (fun w : Word m =>
      weight w = (n + Nat.fib (m + 2)) % Nat.fib (m + 3))) ×ˢ
     ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
      (Finset.univ.filter (fun w : Word m => weight w = n)))).card from
    fun n => by simp only [Finset.card_product]; ring]
  rw [← Finset.card_biUnion]
  · congr 1; ext ⟨v1, v2, v3⟩
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro ⟨h1, h2⟩
      have hmod23 : weight v2 % Nat.fib (m + 3) = weight v3 % Nat.fib (m + 3) :=
        Nat.ModEq.add_right_cancel' (Nat.fib (m + 2)) h2
      rw [Nat.mod_eq_of_lt (X.weight_lt_fib v2),
          Nat.mod_eq_of_lt (X.weight_lt_fib v3)] at hmod23
      rw [Nat.mod_eq_of_lt (X.weight_lt_fib v1)] at h1
      exact ⟨weight v2, X.weight_lt_fib v2, h1, rfl, hmod23.symm⟩
    · rintro ⟨n, hn, hw1, hw2, hw3⟩
      refine ⟨?_, ?_⟩
      · show _ % _ = _ % _
        rw [Nat.mod_eq_of_lt (X.weight_lt_fib v1), hw1, hw2]
      · show _ % _ = _ % _; congr 1; omega
  · intro n _ n' _ hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro ⟨_, v2, _⟩ ⟨_, hw2, _⟩ ⟨_, hw2', _⟩
    exact hne (hw2.symm.trans hw2')

set_option maxHeartbeats 800000 in
/-- T_{ftt}(mod) = CCSH + CCSL' (general, all m).
    prop:pom-s3-recurrence -/
theorem tripleCollisionClass_ftt_mod_split (m : Nat) :
    (tripleCollisionClass m false true true).card =
    crossCorrSqHigh m + crossCorrSqLowPrev m := by
  rw [tripleCollisionClass_ftt_eq_sum]
  have hfib : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  -- Simplify ewc((n+F₂)%F) by case split on n < F₁ vs n ≥ F₁
  have hsubst : ∀ n ∈ Finset.range (Nat.fib (m + 3)),
      exactWeightCount m ((n + Nat.fib (m + 2)) % Nat.fib (m + 3)) *
      exactWeightCount m n ^ 2 =
      if n < Nat.fib (m + 1)
      then exactWeightCount m (n + Nat.fib (m + 2)) * exactWeightCount m n ^ 2
      else exactWeightCount m (n - Nat.fib (m + 1)) * exactWeightCount m n ^ 2 := by
    intro n hn; have hn' := Finset.mem_range.mp hn
    split_ifs with hlt
    · rw [Nat.mod_eq_of_lt (by linarith)]
    · push_neg at hlt
      have hge : Nat.fib (m + 3) ≤ n + Nat.fib (m + 2) := by linarith
      have hlt2 : n + Nat.fib (m + 2) - Nat.fib (m + 3) < Nat.fib (m + 3) := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2, show n + Nat.fib (m + 2) - Nat.fib (m + 3) = n - Nat.fib (m + 1) from by omega]
  rw [Finset.sum_congr rfl hsubst, Finset.sum_ite]
  congr 1
  · -- Σ_{n<F₁} ewc(n+F₂)·ewc(n)² = CCSH
    rw [crossCorrSqHigh_range_truncate]
    -- filter(range(F₃), <F₁) = range(F₁)
    congr 1
    · ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega
    · ext n; ring
  · -- Σ_{n≥F₁} ewc(n-F₁)·ewc(n)² = CCSL'
    rw [crossCorrSqLowPrev_range_truncate]
    apply Finset.sum_bij (fun n _ => n - Nat.fib (m + 1))
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hn
      exact Finset.mem_range.mpr (by omega)
    · intro n1 hn1 n2 hn2 h
      simp only [Finset.mem_filter, not_lt] at hn1 hn2; omega
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      exact ⟨k + Nat.fib (m + 1),
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩,
        by simp⟩
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range, not_lt] at hn
      rw [Nat.sub_add_cancel hn.2]

/-- S_3(m+1) = EWT(m+1) + 3·CCSH'(m) + 3·CCSL'(m) (general, for all m).
    prop:pom-s3-recurrence -/
theorem momentSum_three_eq_ewt_plus_ccs (m : Nat) :
    momentSum 3 (m + 1) = exactWeightTriple (m + 1) +
    3 * crossCorrSqHighPrev m + 3 * crossCorrSqLowPrev m := by
  rw [momentSum_three_lastBit_split]
  rw [tripleCollisionClass_fff_eq_exact, exactTripleClass_fff,
      tripleCollisionClass_ttt_eq_exact, exactTripleClass_ttt]
  rw [tripleCollisionClass_fft_mod_split]
  rw [show (tripleCollisionClass m false true false).card =
      crossCorrSqLow m + crossCorrSqHighPrev m from by
    rw [← tripleCollisionClass_swap23 m false false true]
    exact tripleCollisionClass_fft_mod_split m]
  rw [show (tripleCollisionClass m true false false).card =
      crossCorrSqLow m + crossCorrSqHighPrev m from by
    rw [← tripleCollisionClass_swap12 m false true false,
        ← tripleCollisionClass_swap23 m false false true]
    exact tripleCollisionClass_fft_mod_split m]
  rw [tripleCollisionClass_ftt_mod_split]
  rw [show (tripleCollisionClass m true false true).card =
      crossCorrSqHigh m + crossCorrSqLowPrev m from by
    rw [← tripleCollisionClass_swap12 m false true true]
    exact tripleCollisionClass_ftt_mod_split m]
  rw [show (tripleCollisionClass m true true false).card =
      crossCorrSqHigh m + crossCorrSqLowPrev m from by
    rw [← tripleCollisionClass_swap23 m true false true,
        ← tripleCollisionClass_swap12 m false true true]
    exact tripleCollisionClass_ftt_mod_split m]
  linarith [exactWeightTriple_succ m]

-- ══════════════════════════════════════════════════════════════
-- Phase 161: shiftedTriple = Word³ counting version of CCS'
-- ══════════════════════════════════════════════════════════════

/-- Shifted triple count: triples where weights differ by exactly F_{m+1}.
    bridge:shifted-triple-def -/
def shiftedTriple (m : Nat) : Nat :=
  (Finset.univ.filter (fun p : Word m × Word m × Word m =>
    weight p.1 = weight p.2.1 ∧ weight p.2.2 = weight p.1 + Nat.fib (m + 1))).card +
  (Finset.univ.filter (fun p : Word m × Word m × Word m =>
    weight p.1 + Nat.fib (m + 1) = weight p.2.1 ∧ weight p.2.1 = weight p.2.2)).card

/-- shiftedTriple = CCSH' + CCSL'.
    bridge:shifted-triple-eq -/
theorem shiftedTriple_eq_ccs_prime (m : Nat) :
    shiftedTriple m = crossCorrSqHighPrev m + crossCorrSqLowPrev m := by
  classical
  simp only [shiftedTriple]; congr 1
  · -- CCSH' = Σ_n ewc(n)²·ewc(n+F₁): group by n = wt(v1) = wt(v2)
    simp only [crossCorrSqHighPrev, exactWeightCount]
    simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card ^ 2 *
      (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 1))).card =
      ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
       ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
        (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 1))))).card from
      fun n => by simp only [Finset.card_product]; ring]
    rw [← Finset.card_biUnion]
    · congr 1; ext ⟨v1, v2, v3⟩
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h12, h3⟩ => ⟨weight v1, X.weight_lt_fib v1, rfl, h12.symm, by omega⟩,
        fun ⟨n, _, hw1, hw2, hw3⟩ => ⟨by omega, by omega⟩⟩
    · intro n _ n' _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro ⟨v1, _, _⟩ ⟨hw1, _⟩ ⟨hw1', _⟩; exact hne (hw1.symm.trans hw1')
  · -- CCSL' = Σ_n ewc(n)·ewc(n+F₁)²: group by n = wt(v1)
    simp only [crossCorrSqLowPrev, exactWeightCount]
    simp_rw [show ∀ n, (Finset.univ.filter (fun w : Word m => weight w = n)).card *
      (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 1))).card ^ 2 =
      ((Finset.univ.filter (fun w : Word m => weight w = n)) ×ˢ
       ((Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 1))) ×ˢ
        (Finset.univ.filter (fun w : Word m => weight w = n + Nat.fib (m + 1))))).card from
      fun n => by simp only [Finset.card_product]; ring]
    rw [← Finset.card_biUnion]
    · congr 1; ext ⟨v1, v2, v3⟩
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h23⟩ => ⟨weight v1, X.weight_lt_fib v1, rfl, by omega, by omega⟩,
        fun ⟨n, _, hw1, hw2, hw3⟩ => ⟨by omega, by omega⟩⟩
    · intro n _ n' _ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_product, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro ⟨v1, _, _⟩ ⟨hw1, _⟩ ⟨hw1', _⟩; exact hne (hw1.symm.trans hw1')

-- ══════════════════════════════════════════════════════════════
-- Phase 154: S_3 conditional recurrence consequence chain
-- ══════════════════════════════════════════════════════════════

/-- S_3 subtraction form (conditional).
    prop:pom-s3-recurrence -/
theorem momentSum_three_recurrence_sub_of
    (hrec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1))
    (m : Nat) :
    momentSum 3 (m + 3) = 2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1) -
      2 * momentSum 3 m := by
  have := hrec m; omega

/-- S_3 is strictly monotone (conditional on recurrence).
    prop:pom-s3-recurrence -/
theorem momentSum_three_strict_mono_of
    (hrec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1))
    (m : Nat) :
    momentSum 3 m < momentSum 3 (m + 1) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => rw [← cMomentSum_eq, ← cMomentSum_eq]; simp
    | 1 => rw [← cMomentSum_eq, ← cMomentSum_eq]; simp
    | 2 => rw [← cMomentSum_eq, ← cMomentSum_eq]; simp
    | m + 3 =>
      -- S_3(m+4) = 2·S_3(m+3) + 4·S_3(m+2) - 2·S_3(m+1)
      -- S_3(m+3) = 2·S_3(m+2) + 4·S_3(m+1) - 2·S_3(m)
      -- S_3(m+4) - S_3(m+3) = 2·(S_3(m+3)-S_3(m+2)) + 4·(S_3(m+2)-S_3(m+1)) - 2·(S_3(m+1)-S_3(m))
      -- By IH all differences are positive
      have hrec1 := hrec (m + 1)
      have hrec0 := hrec m
      have h1 := ih (m + 2) (by omega)
      have h2 := ih (m + 1) (by omega)
      have h3 := ih m (by omega)
      -- S(m+4) = 2·S(m+3) + 4·S(m+2) - 2·S(m+1) > S(m+3) since
      -- S(m+3) + 4·S(m+2) > 2·S(m+1) (by monotonicity S(m+2) > S(m+1))
      nlinarith

/-- S_3(m+1) ≥ 2·S_3(m) for m ≥ 2 (conditional).
    prop:pom-s3-recurrence -/
theorem momentSum_three_double_of
    (hrec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1))
    (m : Nat) (hm : 2 ≤ m) :
    2 * momentSum 3 m ≤ momentSum 3 (m + 1) := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 => omega
    | 2 => rw [← cMomentSum_eq, ← cMomentSum_eq]; simp
    | 3 => rw [← cMomentSum_eq, ← cMomentSum_eq]; simp
    | 4 => rw [← cMomentSum_eq, ← cMomentSum_eq]; simp
    | m + 5 =>
      -- S_3(m+6) = 2·S_3(m+5) + 4·S_3(m+4) - 2·S_3(m+3)
      have hrec2 := hrec (m + 3)
      have h1 := ih (m + 4) (by omega) (by omega)
      have h2 := ih (m + 3) (by omega) (by omega)
      have hmono := momentSum_three_strict_mono_of hrec (m + 3)
      nlinarith


/-- S_3(8) = 7768 (by conditional recurrence from S_3(5..7)).
    prop:pom-s3-recurrence -/
theorem momentSum_three_eight_of
    (hrec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1)) :
    momentSum 3 8 = 7768 := by
  have h := hrec 5
  simp only [show (5 : Nat) + 3 = 8 from rfl, show (5 : Nat) + 2 = 7 from rfl,
    show (5 : Nat) + 1 = 6 from rfl,
    momentSum_three_five, momentSum_three_six, momentSum_three_seven] at h; omega

/-- S_3(9) = 23912.
    prop:pom-s3-recurrence -/
theorem momentSum_three_nine_of
    (hrec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1)) :
    momentSum 3 9 = 23912 := by
  have h := hrec 6
  simp only [show (6 : Nat) + 3 = 9 from rfl, show (6 : Nat) + 2 = 8 from rfl,
    show (6 : Nat) + 1 = 7 from rfl,
    momentSum_three_six, momentSum_three_seven, momentSum_three_eight_of hrec] at h; omega

/-- S_3(10) = 73888.
    prop:pom-s3-recurrence -/
theorem momentSum_three_ten_of
    (hrec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1)) :
    momentSum 3 10 = 73888 := by
  have h := hrec 7
  simp only [show (7 : Nat) + 3 = 10 from rfl, show (7 : Nat) + 2 = 9 from rfl,
    show (7 : Nat) + 1 = 8 from rfl,
    momentSum_three_seven, momentSum_three_eight_of hrec, momentSum_three_nine_of hrec] at h; omega

/-- S_3(m) is even for m ≥ 1 (conditional).
    prop:pom-s3-recurrence -/
theorem momentSum_three_even_of
    (hrec : ∀ m, momentSum 3 (m + 3) + 2 * momentSum 3 m =
      2 * momentSum 3 (m + 2) + 4 * momentSum 3 (m + 1))
    (m : Nat) (hm : 1 ≤ m) : 2 ∣ momentSum 3 m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    match m with
    | 0 => omega
    | 1 => exact ⟨1, by rw [momentSum_three_one]⟩
    | 2 => exact ⟨5, by rw [momentSum_three_two]⟩
    | m + 3 =>
      have h := hrec m
      have hmono := momentSum_three_strict_mono_of hrec m
      have hmono2 := momentSum_three_strict_mono_of hrec (m + 1)
      exact ⟨momentSum 3 (m + 2) + 2 * momentSum 3 (m + 1) - momentSum 3 m, by omega⟩

end Omega
