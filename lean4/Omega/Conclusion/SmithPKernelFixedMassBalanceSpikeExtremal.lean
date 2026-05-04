import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

lemma conclusion_smith_pkernel_fixedmass_balance_spike_extremal_min_sum_le_sum_min
    {ι : Type*} (t : Finset ι) (a : ℕ) (f : ι → ℕ) :
    Nat.min a (∑ i ∈ t, f i) ≤ ∑ i ∈ t, Nat.min a (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp
  | insert x t hxt ih =>
      rw [Finset.sum_insert hxt, Finset.sum_insert hxt]
      have hsplit :
          Nat.min a (f x + ∑ i ∈ t, f i) ≤
            Nat.min a (f x) + Nat.min a (∑ i ∈ t, f i) := by
        by_cases hx : a ≤ f x
        · simpa only [Nat.min_eq_left hx] using
            (Nat.min_le_left a (f x + ∑ i ∈ t, f i)).trans
              (Nat.le_add_right a (Nat.min a (∑ i ∈ t, f i)))
        · have hxle : f x ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge hx)
          by_cases ht : a ≤ ∑ i ∈ t, f i
          · simpa only [Nat.min_eq_right hxle, Nat.min_eq_left ht] using
              (Nat.min_le_left a (f x + ∑ i ∈ t, f i)).trans (by omega)
          · have htle : ∑ i ∈ t, f i ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge ht)
            simpa only [Nat.min_eq_right hxle, Nat.min_eq_right htle] using
              Nat.min_le_right a (f x + ∑ i ∈ t, f i)
      exact hsplit.trans (Nat.add_le_add_left ih _)

/-- Paper label: `thm:conclusion-smith-pkernel-fixedmass-balance-spike-extremal`. -/
theorem paper_conclusion_smith_pkernel_fixedmass_balance_spike_extremal
    (E s q r k : ℕ) (lam : Fin s → ℕ) (hs : 0 < s) (hparts : ∀ i, 0 < lam i)
    (hsum : (∑ i : Fin s, lam i) = E) (hdiv : E = s * q + r) (hr : r < s) :
    (s - 1) * Nat.min k 1 + Nat.min k (E - s + 1) ≤
        (∑ i : Fin s, Nat.min k (lam i)) ∧
      (∑ i : Fin s, Nat.min k (lam i)) ≤
        (s - r) * Nat.min k q + r * Nat.min k (q + 1) := by
  have hEge : s ≤ E := by
    have hsum_ge : (∑ i : Fin s, 1) ≤ ∑ i : Fin s, lam i := by
      exact Finset.sum_le_sum fun i _hi => Nat.succ_le_of_lt (hparts i)
    simpa [hsum] using hsum_ge
  constructor
  · by_cases hk0 : k = 0
    · simp [hk0]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hk1 : 1 ≤ k := Nat.succ_le_of_lt hkpos
      have hleft :
          (s - 1) * Nat.min k 1 + Nat.min k (E - s + 1) =
            s + Nat.min (k - 1) (E - s) := by
        by_cases hcap : k ≤ E - s + 1
        · have hmin₁ : Nat.min k (E - s + 1) = k := Nat.min_eq_left hcap
          have hmin₂ : Nat.min (k - 1) (E - s) = k - 1 := by
            apply Nat.min_eq_left
            omega
          simp only [Nat.min_eq_right hk1, hmin₁, hmin₂]
          omega
        · have hmin₁ : Nat.min k (E - s + 1) = E - s + 1 := by
            apply Nat.min_eq_right
            exact Nat.le_of_lt (Nat.lt_of_not_ge hcap)
          have hmin₂ : Nat.min (k - 1) (E - s) = E - s := by
            apply Nat.min_eq_right
            omega
          simp only [Nat.min_eq_right hk1, hmin₁, hmin₂]
          omega
      have hterm :
          ∀ i : Fin s, Nat.min k (lam i) = 1 + Nat.min (k - 1) (lam i - 1) := by
        intro i
        have hlam : 1 ≤ lam i := Nat.succ_le_of_lt (hparts i)
        by_cases hcap : k ≤ lam i
        · have hmin₁ : Nat.min k (lam i) = k := Nat.min_eq_left hcap
          have hmin₂ : Nat.min (k - 1) (lam i - 1) = k - 1 := by
            apply Nat.min_eq_left
            omega
          rw [hmin₁, hmin₂]
          omega
        · have hmin₁ : Nat.min k (lam i) = lam i := by
            apply Nat.min_eq_right
            exact Nat.le_of_lt (Nat.lt_of_not_ge hcap)
          have hmin₂ : Nat.min (k - 1) (lam i - 1) = lam i - 1 := by
            apply Nat.min_eq_right
            omega
          rw [hmin₁, hmin₂]
          omega
      have hsum_term :
          (∑ i : Fin s, Nat.min k (lam i)) =
            s + ∑ i : Fin s, Nat.min (k - 1) (lam i - 1) := by
        calc
          (∑ i : Fin s, Nat.min k (lam i)) =
              ∑ i : Fin s, (1 + Nat.min (k - 1) (lam i - 1)) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                exact hterm i
          _ = s + ∑ i : Fin s, Nat.min (k - 1) (lam i - 1) := by
                simp [Finset.sum_add_distrib]
      have hsum_sub : (∑ i : Fin s, (lam i - 1)) = E - s := by
        calc
          (∑ i : Fin s, (lam i - 1)) =
              (∑ i : Fin s, lam i) - ∑ i : Fin s, 1 := by
                rw [Finset.sum_tsub_distrib]
                intro i _hi
                exact Nat.succ_le_of_lt (hparts i)
          _ = E - s := by
                simp [hsum]
      have hcap_sum :
          Nat.min (k - 1) (E - s) ≤
            ∑ i : Fin s, Nat.min (k - 1) (lam i - 1) := by
        rw [← hsum_sub]
        simpa using
          (conclusion_smith_pkernel_fixedmass_balance_spike_extremal_min_sum_le_sum_min
            (Finset.univ : Finset (Fin s)) (k - 1) fun i => lam i - 1)
      rw [hleft, hsum_term]
      exact Nat.add_le_add_left hcap_sum s
  · by_cases hkq : k ≤ q
    · have hsum_le : (∑ i : Fin s, Nat.min k (lam i)) ≤ ∑ _i : Fin s, k := by
        exact Finset.sum_le_sum fun i _hi => Nat.min_le_left k (lam i)
      have hright :
          (s - r) * Nat.min k q + r * Nat.min k (q + 1) = s * k := by
        simp only [Nat.min_eq_left hkq, Nat.min_eq_left (hkq.trans (Nat.le_succ q))]
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hr)]
      calc
        (∑ i : Fin s, Nat.min k (lam i)) ≤ ∑ _i : Fin s, k := hsum_le
        _ = s * k := by simp
        _ = (s - r) * Nat.min k q + r * Nat.min k (q + 1) := hright.symm
    · have hqk : q < k := Nat.lt_of_not_ge hkq
      have hsum_le : (∑ i : Fin s, Nat.min k (lam i)) ≤ ∑ i : Fin s, lam i := by
        exact Finset.sum_le_sum fun i _hi => Nat.min_le_right k (lam i)
      have hright :
          (s - r) * Nat.min k q + r * Nat.min k (q + 1) = E := by
        simp only [Nat.min_eq_right hqk.le, Nat.min_eq_right (Nat.succ_le_of_lt hqk)]
        rw [hdiv]
        rw [Nat.mul_succ, ← Nat.add_assoc, ← Nat.add_mul,
          Nat.sub_add_cancel (Nat.le_of_lt hr)]
      calc
        (∑ i : Fin s, Nat.min k (lam i)) ≤ ∑ i : Fin s, lam i := hsum_le
        _ = E := hsum
        _ = (s - r) * Nat.min k q + r * Nat.min k (q + 1) := hright.symm

end Omega.Conclusion
