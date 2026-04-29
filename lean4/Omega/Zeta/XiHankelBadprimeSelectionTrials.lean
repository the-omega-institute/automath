import Mathlib
import Omega.Zeta.HankelBadPrimeSelectionProbability

namespace Omega.Zeta

/-- The finite prime set `P(X) = {p ≤ X : p prime}` used for bounded-prime sampling. -/
def xiPrimeSet (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter Nat.Prime

/-- `π(X)` realized as the cardinality of the explicit finite prime set `P(X)`. -/
def xiPrimeCount (X : ℕ) : ℕ :=
  (xiPrimeSet X).card

/-- The bad primes that lie inside the bounded candidate set `P(X)`. -/
def xiHankelBadPrimeSet (Δ X : ℕ) : Finset ℕ :=
  (xiPrimeSet X).filter fun p => p ∈ Δ.primeFactors

/-- The failure ratio for one uniform draw from `P(X)`. -/
def xiHankelBadPrimeFailureRatio (Δ X : ℕ) : ℚ :=
  (xiHankelBadPrimeSet Δ X).card / (xiPrimeCount X : ℚ)

/-- Mean of the geometric law with success probability `1 - q`. -/
def xiHankelGeometricMeanTrials (q : ℚ) : ℚ :=
  1 / (1 - q)

private theorem two_pow_card_le_prod_of_two_le :
    ∀ {s : Finset ℕ}, (∀ p ∈ s, 2 ≤ p) → 2 ^ s.card ≤ ∏ p ∈ s, p := by
  intro s hs
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hs' : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (by simp [hp])
      have ha2 : 2 ≤ a := hs a (by simp [ha])
      calc
        2 ^ (insert a s).card = 2 ^ s.card * 2 := by
          simp [ha, pow_succ, Nat.mul_comm]
        _ ≤ 2 ^ s.card * a := Nat.mul_le_mul_left _ ha2
        _ ≤ a * ∏ p ∈ s, p := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using Nat.mul_le_mul_left a (ih hs')
        _ = ∏ p ∈ insert a s, p := by
          simp [ha]

private theorem primeFactors_card_le_log2 (Δ : ℕ) (hΔ : Δ ≠ 0) :
    Δ.primeFactors.card ≤ Nat.log2 Δ := by
  have hprodLower : 2 ^ Δ.primeFactors.card ≤ ∏ p ∈ Δ.primeFactors, p := by
    apply two_pow_card_le_prod_of_two_le
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hprodDvd : ∏ p ∈ Δ.primeFactors, p ∣ Δ := Nat.prod_primeFactors_dvd Δ
  have hprodLe : ∏ p ∈ Δ.primeFactors, p ≤ Δ := by
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hΔ) hprodDvd
  have hpowLe : 2 ^ Δ.primeFactors.card ≤ Δ := hprodLower.trans hprodLe
  simpa [Nat.log2_eq_log_two] using Nat.le_log_of_pow_le Nat.one_lt_two hpowLe

private lemma xiPrimeCount_pos (X : ℕ) (hX : 2 ≤ X) : 0 < xiPrimeCount X := by
  have htwo_mem : 2 ∈ xiPrimeSet X := by
    rw [xiPrimeSet, Finset.mem_filter]
    refine ⟨?_, Nat.prime_two⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hX)
  exact Finset.card_pos.mpr ⟨2, htwo_mem⟩

/-- Paper label: `cor:xi-hankel-badprime-selection-trials`. Restricting the bad-prime count to the
finite prime set `P(X)` gives the same `ω(Δ)` bound after dividing by `π(X)`, and the repeated
retry scheme is dominated by the geometric law with that failure parameter. -/
theorem paper_xi_hankel_badprime_selection_trials
    (X Δ : ℕ) (hX : 2 ≤ X) (hΔ : Δ ≠ 0) (hbad : Δ.primeFactors.card < xiPrimeCount X) :
    xiHankelBadPrimeFailureRatio Δ X ≤
        (Δ.primeFactors.card : ℚ) / (xiPrimeCount X : ℚ) ∧
      (Δ.primeFactors.card : ℚ) / (xiPrimeCount X : ℚ) ≤
        (Nat.log2 Δ : ℚ) / (xiPrimeCount X : ℚ) ∧
      xiHankelGeometricMeanTrials (xiHankelBadPrimeFailureRatio Δ X) ≤
        xiHankelGeometricMeanTrials
          ((Δ.primeFactors.card : ℚ) / (xiPrimeCount X : ℚ)) := by
  have hcount_pos : 0 < xiPrimeCount X := xiPrimeCount_pos X hX
  have hcount_qpos : (0 : ℚ) < (xiPrimeCount X : ℚ) := by
    exact_mod_cast hcount_pos
  have hsubset : xiHankelBadPrimeSet Δ X ⊆ Δ.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hfail_card : (xiHankelBadPrimeSet Δ X).card ≤ Δ.primeFactors.card := Finset.card_le_card hsubset
  have hfail_le :
      xiHankelBadPrimeFailureRatio Δ X ≤ (Δ.primeFactors.card : ℚ) / (xiPrimeCount X : ℚ) := by
    unfold xiHankelBadPrimeFailureRatio
    exact div_le_div_of_nonneg_right (by exact_mod_cast hfail_card) hcount_qpos.le
  have hω :
      (Δ.primeFactors.card : ℚ) / (xiPrimeCount X : ℚ) ≤
        (Nat.log2 Δ : ℚ) / (xiPrimeCount X : ℚ) := by
    have hcard_le : Δ.primeFactors.card ≤ Nat.log2 Δ := primeFactors_card_le_log2 Δ hΔ
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard_le) hcount_qpos.le
  have hbad_q : (Δ.primeFactors.card : ℚ) < (xiPrimeCount X : ℚ) := by
    exact_mod_cast hbad
  have hden_bound_pos :
      0 < 1 - (Δ.primeFactors.card : ℚ) / (xiPrimeCount X : ℚ) := by
    have hbound_lt_one : (Δ.primeFactors.card : ℚ) / (xiPrimeCount X : ℚ) < 1 := by
      rw [div_lt_one hcount_qpos]
      simpa using hbad_q
    linarith
  have hden_le :
      1 - (Δ.primeFactors.card : ℚ) / (xiPrimeCount X : ℚ) ≤
        1 - xiHankelBadPrimeFailureRatio Δ X := by
    linarith
  refine ⟨hfail_le, hω, ?_⟩
  simpa [xiHankelGeometricMeanTrials] using one_div_le_one_div_of_le hden_bound_pos hden_le

private lemma xiIntervalPrimeCount_pos (Y : ℕ) (hY : 2 ≤ Y) :
    0 < (xiPrimeSet (2 * Y)).card - (xiPrimeSet (Y - 1)).card := by
  have hsubset : xiPrimeSet (Y - 1) ⊆ xiPrimeSet (2 * Y) := by
    intro p hp
    rw [xiPrimeSet, Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hp_range, hp_prime⟩
    refine ⟨?_, hp_prime⟩
    have hp_le : p ≤ Y - 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hp_range)
    exact Finset.mem_range.mpr <| Nat.lt_succ_of_le <| le_trans hp_le (by omega)
  have hproper : xiPrimeSet (Y - 1) ⊂ xiPrimeSet (2 * Y) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, ?_⟩
    intro hEq
    have hY0 : Y ≠ 0 := by omega
    rcases Nat.bertrand Y hY0 with ⟨p, hp_prime, hp_gt, hp_le⟩
    have hp_big : p ∈ xiPrimeSet (2 * Y) := by
      rw [xiPrimeSet, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hp_le), hp_prime⟩
    have hp_small : p ∉ xiPrimeSet (Y - 1) := by
      intro hp
      rw [xiPrimeSet, Finset.mem_filter] at hp
      have hp_le' : p ≤ Y - 1 := Nat.le_of_lt_succ (Finset.mem_range.mp hp.1)
      omega
    exact hp_small (hEq ▸ hp_big)
  exact Nat.sub_pos_of_lt (Finset.card_lt_card hproper)

/-- Paper label: `cor:xi-hankel-badprime-interval-selection-probability`. Restricting the bad
primes to the interval `[Y, 2Y]` only decreases the numerator, while Bertrand's postulate keeps
the interval-prime denominator positive. -/
theorem paper_xi_hankel_badprime_interval_selection_probability
    (Y Delta : Nat) (hY : 2 <= Y) (hDelta : Delta != 0) :
    let intervalPrimeCount := (xiPrimeSet (2 * Y)).card - (xiPrimeSet (Y - 1)).card
    (((Delta.primeFactors.filter fun p => Y <= p /\ p <= 2 * Y).card : Rat) /
        (intervalPrimeCount : Rat) <=
      (Nat.log2 Delta : Rat) / (intervalPrimeCount : Rat)) := by
  dsimp
  have hcount_pos : 0 < (xiPrimeSet (2 * Y)).card - (xiPrimeSet (Y - 1)).card :=
    xiIntervalPrimeCount_pos Y hY
  have hDelta' : Delta ≠ 0 := by
    intro h0
    simp [h0] at hDelta
  have hcount_nonneg :
      (0 : ℚ) ≤
        (((xiPrimeSet (2 * Y)).card - (xiPrimeSet (Y - 1)).card : Nat) : ℚ) := by
    exact_mod_cast hcount_pos.le
  have hbad_card :
      (Delta.primeFactors.filter fun p => Y <= p /\ p <= 2 * Y).card ≤ Nat.log2 Delta := by
    have hfilter :
        (Delta.primeFactors.filter fun p => Y <= p /\ p <= 2 * Y).card ≤ Delta.primeFactors.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact le_trans hfilter (primeFactors_card_le_log2 Delta hDelta')
  exact div_le_div_of_nonneg_right (by exact_mod_cast hbad_card) hcount_nonneg

end Omega.Zeta
