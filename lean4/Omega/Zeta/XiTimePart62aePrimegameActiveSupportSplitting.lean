import Mathlib.Tactic

namespace Omega.Zeta

/-- The part of `n` supported on the finite prime set `S`. -/
def xi_time_part62ae_primegame_active_support_splitting_activeFactor
    (S : Finset ℕ) (n : ℕ) : ℕ :=
  S.prod fun p => p ^ n.factorization p

private lemma xi_time_part62ae_primegame_active_support_splitting_activeFactor_ne_zero
    (S : Finset ℕ) (hSprime : ∀ p ∈ S, Nat.Prime p) (n : ℕ) :
    xi_time_part62ae_primegame_active_support_splitting_activeFactor S n ≠ 0 := by
  rw [xi_time_part62ae_primegame_active_support_splitting_activeFactor,
    Finset.prod_ne_zero_iff]
  intro p hpS
  exact pow_ne_zero _ (hSprime p hpS).ne_zero

private lemma xi_time_part62ae_primegame_active_support_splitting_factorization_prime
    (S : Finset ℕ) (hSprime : ∀ p ∈ S, Nat.Prime p) (n q : ℕ) (hq : Nat.Prime q) :
    (xi_time_part62ae_primegame_active_support_splitting_activeFactor S n).factorization q =
      if q ∈ S then n.factorization q else 0 := by
  rw [xi_time_part62ae_primegame_active_support_splitting_activeFactor,
    Nat.factorization_prod_apply]
  · by_cases hqS : q ∈ S
    · rw [if_pos hqS]
      rw [Finset.sum_eq_single q]
      · simp [Nat.factorization_pow, hq.factorization_self]
      · intro p hpS hpne
        have hp : Nat.Prime p := hSprime p hpS
        simp [hp.factorization_pow, hpne]
      · intro hq_not_mem
        exact (hq_not_mem hqS).elim
    · rw [if_neg hqS]
      refine Finset.sum_eq_zero ?_
      intro p hpS
      have hp : Nat.Prime p := hSprime p hpS
      have hpne : p ≠ q := by
        intro hpq
        exact hqS (hpq ▸ hpS)
      simp [hp.factorization_pow, hpne]
  · intro p hpS
    exact pow_ne_zero _ (hSprime p hpS).ne_zero

/-- Paper label: `thm:xi-time-part62ae-primegame-active-support-splitting`. -/
theorem paper_xi_time_part62ae_primegame_active_support_splitting
    (S : Finset ℕ) (hSprime : ∀ p ∈ S, Nat.Prime p) (n : ℕ) (hn : 0 < n) :
    ∃! um : ℕ × ℕ,
      n = um.1 * um.2 ∧
        (∀ p : ℕ, Nat.Prime p → p ∣ um.1 → p ∈ S) ∧
          (∀ p ∈ S, ¬ p ∣ um.2) := by
  let u := xi_time_part62ae_primegame_active_support_splitting_activeFactor S n
  let m := n / u
  have hn_ne : n ≠ 0 := hn.ne'
  have hu_ne : u ≠ 0 :=
    xi_time_part62ae_primegame_active_support_splitting_activeFactor_ne_zero S hSprime n
  have hu_pos : 0 < u := Nat.pos_of_ne_zero hu_ne
  have hu_dvd : u ∣ n := by
    refine (Nat.factorization_prime_le_iff_dvd hu_ne hn_ne).mp ?_
    intro q hq
    rw [xi_time_part62ae_primegame_active_support_splitting_factorization_prime S hSprime n q hq]
    by_cases hqS : q ∈ S
    · simp [hqS]
    · simp [hqS]
  have hmul : u * m = n := by
    exact Nat.mul_div_cancel' hu_dvd
  refine ⟨(u, m), ?_, ?_⟩
  · refine ⟨hmul.symm, ?_, ?_⟩
    · intro p hp hpu
      by_contra hpS
      have hpos : 1 ≤ u.factorization p :=
        (hp.dvd_iff_one_le_factorization hu_ne).mp hpu
      rw [xi_time_part62ae_primegame_active_support_splitting_factorization_prime S hSprime n p hp,
        if_neg hpS] at hpos
      omega
    · intro p hpS
      have hp : Nat.Prime p := hSprime p hpS
      have hm_ne : m ≠ 0 := by
        intro hm0
        have : n = 0 := by
          rw [← hmul, hm0, mul_zero]
        exact hn_ne this
      intro hpm
      have hpos : 1 ≤ m.factorization p :=
        (hp.dvd_iff_one_le_factorization hm_ne).mp hpm
      have hufac : u.factorization p = n.factorization p := by
        dsimp [u]
        rw [xi_time_part62ae_primegame_active_support_splitting_factorization_prime S hSprime n p hp,
          if_pos hpS]
      have hmfac : m.factorization p = 0 := by
        change (n / u).factorization p = 0
        rw [Nat.factorization_div hu_dvd]
        change n.factorization p - u.factorization p = 0
        simp [hufac]
      omega
  · intro y hy
    rcases y with ⟨a, b⟩
    rcases hy with ⟨hny, ha_support, hb_compl⟩
    have ha_ne : a ≠ 0 := by
      intro ha0
      have : n = 0 := by
        rw [hny, ha0, zero_mul]
      exact hn_ne this
    have hb_ne : b ≠ 0 := by
      intro hb0
      have : n = 0 := by
        rw [hny, hb0, mul_zero]
      exact hn_ne this
    have ha_fac_eq : ∀ q, a.factorization q = u.factorization q := by
      intro q
      by_cases hq : Nat.Prime q
      · by_cases hqS : q ∈ S
        · have hbq : b.factorization q = 0 :=
            Nat.factorization_eq_zero_of_not_dvd (hb_compl q hqS)
          have hnfac : n.factorization q = a.factorization q + b.factorization q := by
            rw [hny, Nat.factorization_mul ha_ne hb_ne]
            rfl
          rw [xi_time_part62ae_primegame_active_support_splitting_factorization_prime S hSprime n q hq,
            if_pos hqS]
          omega
        · have haq : a.factorization q = 0 := by
            by_contra hqa
            exact hqS (ha_support q hq (Nat.dvd_of_factorization_pos hqa))
          rw [xi_time_part62ae_primegame_active_support_splitting_factorization_prime S hSprime n q hq,
            if_neg hqS]
          exact haq
      · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
    have hau : a = u := Nat.eq_of_factorization_eq ha_ne hu_ne ha_fac_eq
    have hmb : m = b := by
      apply Nat.mul_left_cancel hu_pos
      rw [hmul, hny, hau]
    ext <;> simp [hau, hmb]

end Omega.Zeta
