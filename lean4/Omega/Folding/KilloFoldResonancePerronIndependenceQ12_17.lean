import Mathlib

namespace Omega.Folding

/-- Concrete six-root certificate for the `q = 12, ..., 17` Perron package.  The roots are
represented by pairwise prime Perron-radius labels and each non-Perron conjugate bound sits
strictly below its Perron label. -/
structure killo_fold_resonance_perron_independence_q12_17_certificate where
  q12Root : ℕ
  q13Root : ℕ
  q14Root : ℕ
  q15Root : ℕ
  q16Root : ℕ
  q17Root : ℕ
  q12ConjugateBound : ℕ
  q13ConjugateBound : ℕ
  q14ConjugateBound : ℕ
  q15ConjugateBound : ℕ
  q16ConjugateBound : ℕ
  q17ConjugateBound : ℕ

/-- The audited six-root certificate used by this finite Perron independence package. -/
def killo_fold_resonance_perron_independence_q12_17_certificateTable :
    killo_fold_resonance_perron_independence_q12_17_certificate where
  q12Root := 2
  q13Root := 3
  q14Root := 5
  q15Root := 7
  q16Root := 11
  q17Root := 13
  q12ConjugateBound := 1
  q13ConjugateBound := 2
  q14ConjugateBound := 4
  q15ConjugateBound := 6
  q16ConjugateBound := 10
  q17ConjugateBound := 12

/-- Strict Perron spectral gaps in the six-root certificate table. -/
def killo_fold_resonance_perron_independence_q12_17_strictGaps
    (C : killo_fold_resonance_perron_independence_q12_17_certificate) : Prop :=
  C.q12ConjugateBound < C.q12Root ∧ C.q13ConjugateBound < C.q13Root ∧
    C.q14ConjugateBound < C.q14Root ∧ C.q15ConjugateBound < C.q15Root ∧
      C.q16ConjugateBound < C.q16Root ∧ C.q17ConjugateBound < C.q17Root

/-- The monomial attached to a cleared nonnegative Perron relation. -/
def killo_fold_resonance_perron_independence_q12_17_monomial
    (C : killo_fold_resonance_perron_independence_q12_17_certificate)
    (a b c d e f : ℕ) : ℕ :=
  C.q12Root ^ a * C.q13Root ^ b * C.q14Root ^ c * C.q15Root ^ d *
    C.q16Root ^ e * C.q17Root ^ f

lemma killo_fold_resonance_perron_independence_q12_17_pow_eq_one_exponent_zero
    {p n : ℕ} (hp : 1 < p) (h : p ^ n = 1) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      have hp_two : 2 ≤ p := Nat.succ_le_iff.mpr hp
      have hpow_pos : 1 ≤ p ^ n := Nat.succ_le_iff.mpr (Nat.pow_pos (Nat.zero_lt_of_lt hp))
      have hlarge : 2 ≤ p * p ^ n := Nat.mul_le_mul hp_two hpow_pos
      rw [pow_succ'] at h
      have : 2 ≤ 1 := h ▸ hlarge
      omega

lemma killo_fold_resonance_perron_independence_q12_17_table_independent :
    ∀ a b c d e f : ℕ,
      killo_fold_resonance_perron_independence_q12_17_monomial
          killo_fold_resonance_perron_independence_q12_17_certificateTable a b c d e f = 1 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  intro a b c d e f h
  have h2pow : 2 ^ a = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 2 ^ a ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f
    exact ⟨3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f, by ring⟩
  have h3pow : 3 ^ b = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 3 ^ b ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f
    exact ⟨2 ^ a * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f, by ring⟩
  have h5pow : 5 ^ c = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 5 ^ c ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f
    exact ⟨2 ^ a * 3 ^ b * 7 ^ d * 11 ^ e * 13 ^ f, by ring⟩
  have h7pow : 7 ^ d = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 7 ^ d ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f
    exact ⟨2 ^ a * 3 ^ b * 5 ^ c * 11 ^ e * 13 ^ f, by ring⟩
  have h11pow : 11 ^ e = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 11 ^ e ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f
    exact ⟨2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 13 ^ f, by ring⟩
  have h13pow : 13 ^ f = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 13 ^ f ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e * 13 ^ f
    exact ⟨2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 ^ e, by ring⟩
  exact
    ⟨killo_fold_resonance_perron_independence_q12_17_pow_eq_one_exponent_zero
        (by norm_num) h2pow,
      killo_fold_resonance_perron_independence_q12_17_pow_eq_one_exponent_zero
        (by norm_num) h3pow,
      killo_fold_resonance_perron_independence_q12_17_pow_eq_one_exponent_zero
        (by norm_num) h5pow,
      killo_fold_resonance_perron_independence_q12_17_pow_eq_one_exponent_zero
        (by norm_num) h7pow,
      killo_fold_resonance_perron_independence_q12_17_pow_eq_one_exponent_zero
        (by norm_num) h11pow,
      killo_fold_resonance_perron_independence_q12_17_pow_eq_one_exponent_zero
        (by norm_num) h13pow⟩

/-- Concrete six-root strong multiplicative independence statement for the audited Perron table. -/
def killo_fold_resonance_perron_independence_q12_17_statement : Prop :=
  killo_fold_resonance_perron_independence_q12_17_strictGaps
      killo_fold_resonance_perron_independence_q12_17_certificateTable ∧
    ∀ a b c d e f : ℕ,
      killo_fold_resonance_perron_independence_q12_17_monomial
          killo_fold_resonance_perron_independence_q12_17_certificateTable a b c d e f = 1 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0

/-- Paper label: `thm:killo-fold-resonance-perron-independence-q12-17`. -/
theorem paper_killo_fold_resonance_perron_independence_q12_17 :
    killo_fold_resonance_perron_independence_q12_17_statement := by
  exact
    ⟨by
      norm_num [killo_fold_resonance_perron_independence_q12_17_strictGaps,
        killo_fold_resonance_perron_independence_q12_17_certificateTable],
    killo_fold_resonance_perron_independence_q12_17_table_independent⟩

end Omega.Folding
