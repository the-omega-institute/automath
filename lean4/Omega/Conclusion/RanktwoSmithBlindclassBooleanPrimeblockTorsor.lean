import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The unitary divisors of `n`: divisors `d` such that `d` is coprime to the complementary
quotient `n / d`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => Nat.Coprime d (n / d)

@[simp]
private theorem mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∈ n.divisors ∧ Nat.Coprime d (n / d) := by
  simp [unitaryDivisors]

private theorem card_unitaryDivisors_prime_pow_mul
    (a p k : ℕ) (hp : p.Prime) (hpa : ¬ p ∣ a) (hk : 0 < k) :
    (unitaryDivisors (p ^ k * a)).card = 2 * (unitaryDivisors a).card := by
  classical
  have ha : a ≠ 0 := by
    intro ha0
    exact hpa (ha0.symm ▸ dvd_zero p)
  have hpow : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hpow_pos : 0 < p ^ k := pow_pos hp.pos _
  have hcop_pa : Nat.Coprime (p ^ k) a :=
    Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpa)
  have hsplit :
      unitaryDivisors (p ^ k * a) =
        unitaryDivisors a ∪ (unitaryDivisors a).image (fun d => p ^ k * d) := by
    ext d
    constructor
    · intro hd
      rcases mem_unitaryDivisors.mp hd with ⟨hd_divs, hd_coprime⟩
      have hd_dvd : d ∣ p ^ k * a := (Nat.mem_divisors.mp hd_divs).1
      by_cases hpd : p ∣ d
      · have hp_coprime_q :
            Nat.Coprime p ((p ^ k * a) / d) := by
          exact Nat.Coprime.of_dvd_left hpd hd_coprime
        have hp_not_dvd_q : ¬ p ∣ (p ^ k * a) / d :=
          hp.coprime_iff_not_dvd.mp hp_coprime_q
        have hpow_dvd : p ^ k ∣ d := by
          have hp' : Prime p := Nat.prime_iff.mp hp
          have : p ^ k ∣ d * ((p ^ k * a) / d) := by
            rw [Nat.mul_div_cancel' hd_dvd]
            exact dvd_mul_right _ _
          exact Prime.pow_dvd_of_dvd_mul_right hp' k hp_not_dvd_q this
        rcases hpow_dvd with ⟨e, rfl⟩
        have he_dvd : e ∣ a := by
          rcases hd_dvd with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          apply Nat.eq_of_mul_eq_mul_left hpow_pos
          simpa [mul_assoc, mul_left_comm, mul_comm] using hc
        have hquot :
            (p ^ k * a) / (p ^ k * e) = a / e := by
          have hmul : (p ^ k * e) * ((p ^ k * a) / (p ^ k * e)) = p ^ k * a :=
            Nat.mul_div_cancel' hd_dvd
          have hcancel : e * ((p ^ k * a) / (p ^ k * e)) = a := by
            apply Nat.eq_of_mul_eq_mul_left hpow_pos
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          symm
          exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero ha he_dvd)
            (by simpa [mul_comm] using hcancel.symm)
        have he_coprime : Nat.Coprime e (a / e) := by
          have : Nat.Coprime e ((p ^ k * a) / (p ^ k * e)) :=
            Nat.Coprime.of_dvd_left (dvd_mul_left _ _) hd_coprime
          exact hquot ▸ this
        refine Finset.mem_union.mpr <| Or.inr ?_
        exact Finset.mem_image.mpr ⟨e, mem_unitaryDivisors.mpr
          ⟨Nat.mem_divisors.mpr ⟨he_dvd, ha⟩, he_coprime⟩, by simp⟩
      · have hd_coprime_pow : Nat.Coprime d (p ^ k) := by
          exact Nat.Coprime.pow_right k (hp.coprime_iff_not_dvd.mpr hpd).symm
        have hd_a : d ∣ a := hd_coprime_pow.dvd_of_dvd_mul_left hd_dvd
        have hd_coprime_a : Nat.Coprime d (a / d) := by
          apply hd_coprime.coprime_dvd_right
          rw [Nat.mul_div_assoc _ hd_a]
          exact dvd_mul_left _ _
        refine Finset.mem_union.mpr <| Or.inl ?_
        exact mem_unitaryDivisors.mpr
          ⟨Nat.mem_divisors.mpr ⟨hd_a, ha⟩, hd_coprime_a⟩
    · intro hd
      rcases Finset.mem_union.mp hd with hd | hd
      · rcases mem_unitaryDivisors.mp hd with ⟨hd_divs, hd_coprime⟩
        have hd_a : d ∣ a := (Nat.mem_divisors.mp hd_divs).1
        have hd_not_dvd_p : ¬ p ∣ d := by
          intro h
          exact hpa (dvd_trans h hd_a)
        have hd_coprime_pow : Nat.Coprime d (p ^ k) := by
          exact Nat.Coprime.pow_right k (hp.coprime_iff_not_dvd.mpr hd_not_dvd_p).symm
        refine mem_unitaryDivisors.mpr ?_
        constructor
        · exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_right hd_a _, mul_ne_zero hpow ha⟩
        · rw [Nat.mul_div_assoc _ hd_a]
          exact hd_coprime_pow.mul_right hd_coprime
      · rcases Finset.mem_image.mp hd with ⟨e, he, rfl⟩
        rcases mem_unitaryDivisors.mp he with ⟨he_divs, he_coprime⟩
        have he_a : e ∣ a := (Nat.mem_divisors.mp he_divs).1
        have he0 : e ≠ 0 := ne_zero_of_dvd_ne_zero ha he_a
        have hdiv : p ^ k * e ∣ p ^ k * a := by
          rcases he_a with ⟨c, rfl⟩
          exact ⟨c, by ac_rfl⟩
        have hquot : (p ^ k * a) / (p ^ k * e) = a / e := by
          refine Nat.div_eq_of_eq_mul_left (Nat.mul_pos hpow_pos (Nat.pos_of_ne_zero he0)) ?_
          calc
            p ^ k * a = p ^ k * (e * (a / e)) := by
              rw [Nat.mul_div_cancel' he_a]
            _ = (a / e) * (p ^ k * e) := by
              ac_rfl
        have hp_coprime_ae : Nat.Coprime (p ^ k) (a / e) := by
          apply Nat.Coprime.pow_left k
          apply Nat.Coprime.of_dvd_right (Nat.div_dvd_of_dvd he_a)
          exact hp.coprime_iff_not_dvd.mpr hpa
        have hprod_coprime : Nat.Coprime (p ^ k * e) (a / e) := by
          rw [Nat.coprime_mul_iff_left]
          exact ⟨hp_coprime_ae, he_coprime⟩
        refine mem_unitaryDivisors.mpr ?_
        constructor
        · exact Nat.mem_divisors.mpr ⟨hdiv, mul_ne_zero hpow ha⟩
        · simpa [hquot] using hprod_coprime
  have hdisj :
      Disjoint (unitaryDivisors a) ((unitaryDivisors a).image (fun d => p ^ k * d)) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    rcases Finset.mem_image.mp hx' with ⟨e, he, hxe⟩
    have hx_a : x ∣ a := (Nat.mem_divisors.mp ((mem_unitaryDivisors.mp hx).1)).1
    have hx_not_dvd_p : ¬ p ∣ x := by
      intro h
      exact hpa (dvd_trans h hx_a)
    have hx_dvd_p : p ∣ x := by
      have : p ∣ p ^ k * e := dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.ne_of_gt hk)) _
      simpa [hxe] using this
    exact hx_not_dvd_p hx_dvd_p
  rw [hsplit, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective (unitaryDivisors a)]
  · omega
  · intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hpow_pos (by simpa [mul_comm] using hxy)

private theorem unitaryDivisors_card_or_zero (n : ℕ) :
    n = 0 ∨ (unitaryDivisors n).card = 2 ^ n.primeFactors.card := by
  refine Nat.recOnPrimePow ?_ ?_ ?_ n
  · exact Or.inl rfl
  · right
    native_decide
  · intro a p k hp hpa hk ha
    have ha0 : a ≠ 0 := by
      intro h
      exact hpa (h.symm ▸ dvd_zero p)
    rcases ha with rfl | ha
    · exact (hpa (dvd_zero p)).elim
    right
    rw [card_unitaryDivisors_prime_pow_mul a p k hp hpa hk, ha]
    have hcop : Nat.Coprime (p ^ k) a :=
      Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hpa)
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    calc
      2 * 2 ^ a.primeFactors.card = 2 ^ (a.primeFactors.card + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      _ = 2 ^ (a.primeFactors.card + ({p} : Finset ℕ).card) := by simp
      _ = 2 ^ ((p ^ k * a).primeFactors.card) := by
        congr 1
        rw [Nat.Coprime.primeFactors_mul hcop, Nat.primeFactors_prime_pow hk0 hp,
          Finset.card_union_of_disjoint]
        · omega
        · exact Finset.disjoint_singleton_left.mpr fun hp_mem => hpa (Nat.dvd_of_mem_primeFactors hp_mem)

private theorem unitaryDivisors_card {n : ℕ} (hn : n ≠ 0) :
    (unitaryDivisors n).card = 2 ^ n.primeFactors.card := by
  rcases unitaryDivisors_card_or_zero n with rfl | h
  · contradiction
  · exact h

/-- The requested paper theorem is false without the positivity hypothesis `a, b > 0` from the
paper statement: at `(a, b) = (0, 0)` the left-hand side is `0` while the right-hand side is `1`.
-/
theorem paper_conclusion_ranktwo_smith_blindclass_boolean_primeblock_torsor_counterexample :
    let g := Nat.gcd 0 0
    let l := Nat.lcm 0 0
    let h := l / g
    (h.divisors.filter fun u => Nat.Coprime u (h / u)).card ≠ 2 ^ h.primeFactors.card := by
  simp

/-- The coprime divisor pairs of `h = l / g` are the unitary divisors of `h`, so each prime-power
block of `h` can be assigned independently to one side or the other. -/
theorem paper_conclusion_ranktwo_smith_blindclass_boolean_primeblock_torsor
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    let g := Nat.gcd a b
    let l := Nat.lcm a b
    let h := l / g
    (h.divisors.filter fun u => Nat.Coprime u (h / u)).card = 2 ^ h.primeFactors.card := by
  dsimp
  have hg_pos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
  have hl_pos : 0 < Nat.lcm a b := Nat.lcm_pos ha hb
  have hg_dvd_l : Nat.gcd a b ∣ Nat.lcm a b := by
    exact dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_lcm_left a b)
  have hh_pos : 0 < Nat.lcm a b / Nat.gcd a b :=
    Nat.div_pos (Nat.le_of_dvd hl_pos hg_dvd_l) hg_pos
  simpa [unitaryDivisors] using
    unitaryDivisors_card (n := Nat.lcm a b / Nat.gcd a b) hh_pos.ne'

end Omega.Conclusion
