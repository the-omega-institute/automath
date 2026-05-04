import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

private lemma conclusion_primeslice_v2_layer_spread_inventory_odd_part_exists
    {t : ℕ} (ht : 0 < t) :
    ∃ n : ℕ, 0 < n ∧ t = 2 ^ padicValNat 2 t * (2 * n - 1) := by
  let j := padicValNat 2 t
  have hpow_dvd : 2 ^ j ∣ t := pow_padicValNat_dvd
  rcases hpow_dvd with ⟨q, hq⟩
  have ht_eq : t = 2 ^ j * q := hq
  have hq_pos : 0 < q := by
    refine Nat.pos_iff_ne_zero.mpr ?_
    intro hq_zero
    rw [hq_zero, mul_zero] at ht_eq
    omega
  have hq_not_two_dvd : ¬ 2 ∣ q := by
    intro htwo
    have hsucc_dvd : 2 ^ (j + 1) ∣ t := by
      rw [ht_eq, pow_succ]
      exact Nat.mul_dvd_mul_left (2 ^ j) htwo
    exact pow_succ_padicValNat_not_dvd (p := 2) ht.ne' hsucc_dvd
  have hq_odd : Odd q := Nat.not_even_iff_odd.mp fun hEven => hq_not_two_dvd hEven.two_dvd
  rcases (odd_iff_exists_bit1.mp hq_odd) with ⟨m, hm⟩
  refine ⟨m + 1, Nat.succ_pos m, ?_⟩
  rw [show 2 * (m + 1) - 1 = q by omega]
  exact ht_eq

private lemma conclusion_primeslice_v2_layer_spread_inventory_padicVal_eq_of_repr
    {t j n : ℕ} (hn : 0 < n) (hrepr : t = 2 ^ j * (2 * n - 1)) :
    padicValNat 2 t = j := by
  let q := 2 * n - 1
  have hq_pos : 0 < q := by
    dsimp [q]
    omega
  have hq_odd : Odd q := by
    refine odd_iff_exists_bit1.mpr ⟨n - 1, ?_⟩
    dsimp [q]
    omega
  have hq_val : padicValNat 2 q = 0 :=
    padicValNat.eq_zero_of_not_dvd hq_odd.not_two_dvd_nat
  calc
    padicValNat 2 t = padicValNat 2 (2 ^ j * q) := by rw [hrepr]
    _ = padicValNat 2 (2 ^ j) + padicValNat 2 q := by
      rw [padicValNat.mul] <;> positivity
    _ = j := by
      simp [q, hq_val, padicValNat.prime_pow]

/-- Paper label: `thm:conclusion-primeslice-v2-layer-spread-inventory`. -/
theorem paper_conclusion_primeslice_v2_layer_spread_inventory
    (Λ : Finset ℕ) (hΛ : ∀ t ∈ Λ, 0 < t) :
    (∀ t ∈ Λ, ∃! j, ∃ n : ℕ, 0 < n ∧ t = 2 ^ j * (2 * n - 1)) := by
  intro t htΛ
  refine ⟨padicValNat 2 t, conclusion_primeslice_v2_layer_spread_inventory_odd_part_exists
    (hΛ t htΛ), ?_⟩
  intro j hj
  rcases hj with ⟨n, hn, hrepr⟩
  exact (conclusion_primeslice_v2_layer_spread_inventory_padicVal_eq_of_repr hn hrepr).symm

end Omega.Conclusion
