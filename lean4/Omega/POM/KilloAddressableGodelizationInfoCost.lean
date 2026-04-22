import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality

namespace Omega.POM

/-- Choose a symbol in `Fin A` different from the prescribed input. The hypothesis `2 ≤ A` makes
the two fallback symbols `0` and `1` available. -/
def killo_addressable_godelization_info_cost_choose_away {A : ℕ} (hA : 2 ≤ A) : Fin A → Fin A
  | ⟨0, _h0⟩ => ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hA⟩
  | ⟨n + 1, hn⟩ => ⟨0, lt_trans (Nat.succ_pos n) hn⟩

lemma killo_addressable_godelization_info_cost_choose_away_ne {A : ℕ} (hA : 2 ≤ A)
    (a : Fin A) :
    killo_addressable_godelization_info_cost_choose_away hA a ≠ a := by
  rcases a with ⟨n, ha⟩
  cases n with
  | zero =>
      simp [killo_addressable_godelization_info_cost_choose_away]
  | succ n =>
      simp [killo_addressable_godelization_info_cost_choose_away]

/-- The worst-case addressable word obtained by moving every coordinate away from the decoder value
seen at valuation `0`. -/
def killo_addressable_godelization_info_cost_worst_word {A T : ℕ} (hA : 2 ≤ A)
    (decoder : Fin T → ℕ → Fin A) : Fin T → Fin A :=
  fun i => killo_addressable_godelization_info_cost_choose_away hA (decoder i 0)

/-- Paper label: `prop:killo-addressable-godelization-info-cost`.
Choosing each coordinate away from the decoder output at valuation `0` forces every prime
valuation to be positive, so the resulting Gödel code is divisible by `T` distinct primes and
hence has the expected `Ω(T log T)` logarithmic size. -/
theorem paper_killo_addressable_godelization_info_cost {A T : ℕ} (hA : 2 ≤ A) (hT : 0 < T)
    (p : Fin T → ℕ) (decoder : Fin T → ℕ → Fin A) (code : (Fin T → Fin A) → ℕ)
    (hprime : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hdecode : ∀ s i, decoder i (Nat.factorization (code s) (p i)) = s i) :
    ∃ sstar : Fin T → Fin A,
      (∀ i, 1 ≤ Nat.factorization (code sstar) (p i)) ∧
        firstPrimeProduct T ≤ code sstar ∧
          ((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
              Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2 ≤
            Real.log (code sstar)) := by
  let sstar : Fin T → Fin A :=
    killo_addressable_godelization_info_cost_worst_word hA decoder
  have hsstar_fac : ∀ i, 1 ≤ Nat.factorization (code sstar) (p i) := by
    intro i
    have hneq :
        sstar i ≠ decoder i 0 := by
      exact killo_addressable_godelization_info_cost_choose_away_ne hA (decoder i 0)
    have hfac_ne :
        Nat.factorization (code sstar) (p i) ≠ 0 := by
      intro hzero
      have hdecoded := hdecode sstar i
      rw [hzero] at hdecoded
      exact hneq hdecoded.symm
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hfac_ne)
  have hsstar_dvd : ∀ i, p i ∣ code sstar := by
    intro i
    exact Nat.dvd_of_factorization_pos (Nat.ne_of_gt (hsstar_fac i))
  have hpair : Pairwise fun i j : Fin T => Nat.Coprime (p i) (p j) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).2 fun hpij => hij (hinj hpij)
  have hsstar_ne_zero : code sstar ≠ 0 := by
    intro hzero
    have hfac := hsstar_fac ⟨0, hT⟩
    simp [hzero] at hfac
  have hq : ∀ i, 2 ≤ p i := fun i => (hprime i).two_le
  have hledger_factorization_at : ∀ i, (ledgerProduct p).factorization (p i) = 1 := by
    intro i
    unfold ledgerProduct
    rw [Nat.factorization_prod_apply]
    · have hfac : ∀ j : Fin T, (p j).factorization (p i) = if j = i then 1 else 0 := by
        intro j
        by_cases hji : j = i
        · subst hji
          simpa using (Nat.Prime.factorization_self (hprime j))
        · have hneq : p j ≠ p i := by
            exact fun hpij => hji (hinj hpij)
          simpa [hji, hneq] using congrArg (fun f => f (p i)) (Nat.Prime.factorization (hprime j))
      simp [hfac]
    · intro j hj
      exact Nat.ne_of_gt (hprime j).pos
  have hledger_factorization_zero {q : ℕ} (hq : ∀ i : Fin T, p i ≠ q) :
      (ledgerProduct p).factorization q = 0 := by
    unfold ledgerProduct
    rw [Nat.factorization_prod_apply]
    · have hfac : ∀ j : Fin T, (p j).factorization q = 0 := by
        intro j
        simpa [hq j] using congrArg (fun f => f q) (Nat.Prime.factorization (hprime j))
      simp [hfac]
    · intro j hj
      exact Nat.ne_of_gt (hprime j).pos
  have hledger_dvd : ledgerProduct p ∣ code sstar := by
    refine (Nat.factorization_le_iff_dvd (Nat.ne_of_gt (ledgerProduct_pos p hq)) hsstar_ne_zero).1 ?_
    intro q
    by_cases hqeq : ∃ i : Fin T, p i = q
    · rcases hqeq with ⟨i, rfl⟩
      rw [hledger_factorization_at i]
      exact hsstar_fac i
    · rw [hledger_factorization_zero (q := q) (fun i hi => hqeq ⟨i, hi⟩)]
      exact Nat.zero_le _
  have hledger_le_code : ledgerProduct p ≤ code sstar := by
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero hsstar_ne_zero) hledger_dvd
  have hprimorial_le : firstPrimeProduct T ≤ ledgerProduct p :=
    (paper_pom_coprime_ledger_primorial_optimality T 1 p hq hpair).2.1
  have hfirstPrimeProduct_le_code : firstPrimeProduct T ≤ code sstar := by
    exact le_trans hprimorial_le hledger_le_code
  have hstirling :
      ((T + 1 : ℝ) * Real.log (T + 1) - (T + 1) +
          Real.log (T + 1) / 2 + Real.log (2 * Real.pi) / 2) ≤
        Real.log (firstPrimeProduct T) :=
    (paper_pom_coprime_ledger_primorial_optimality T 1 p hq hpair).2.2
  have hlog_le : Real.log (firstPrimeProduct T) ≤ Real.log (code sstar) := by
    have hfirstPrimeProduct_pos : 0 < (firstPrimeProduct T : ℝ) := by
      exact_mod_cast firstPrimeProduct_pos T
    exact Real.log_le_log hfirstPrimeProduct_pos (by exact_mod_cast hfirstPrimeProduct_le_code)
  refine ⟨sstar, hsstar_fac, hfirstPrimeProduct_le_code, ?_⟩
  linarith

end Omega.POM
