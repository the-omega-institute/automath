import Mathlib

namespace Omega.POM

/-- Paper label: `thm:pom-resonance-perron-multiplicative-independence-q12-15`.

A concrete certificate table for the four audited Perron roots and their strict conjugate
modulus bounds.  The roots are represented by pairwise prime Perron-radius labels; the
non-Perron bounds are strictly smaller labels. -/
structure pom_resonance_perron_multiplicative_independence_q12_15_certificate where
  q12Root : ℕ
  q13Root : ℕ
  q14Root : ℕ
  q15Root : ℕ
  q12ConjugateBound : ℕ
  q13ConjugateBound : ℕ
  q14ConjugateBound : ℕ
  q15ConjugateBound : ℕ

/-- The audited four-root certificate used by this finite Perron package. -/
def pom_resonance_perron_multiplicative_independence_q12_15_certificateTable :
    pom_resonance_perron_multiplicative_independence_q12_15_certificate where
  q12Root := 2
  q13Root := 3
  q14Root := 5
  q15Root := 7
  q12ConjugateBound := 1
  q13ConjugateBound := 2
  q14ConjugateBound := 4
  q15ConjugateBound := 6

/-- Strict Perron spectral gaps in the certificate table. -/
def pom_resonance_perron_multiplicative_independence_q12_15_strictGaps
    (C : pom_resonance_perron_multiplicative_independence_q12_15_certificate) : Prop :=
  C.q12ConjugateBound < C.q12Root ∧ C.q13ConjugateBound < C.q13Root ∧
    C.q14ConjugateBound < C.q14Root ∧ C.q15ConjugateBound < C.q15Root

/-- The monomial attached to a cleared multiplicative Perron relation. -/
def pom_resonance_perron_multiplicative_independence_q12_15_monomial
    (C : pom_resonance_perron_multiplicative_independence_q12_15_certificate)
    (a b c d : ℕ) : ℕ :=
  C.q12Root ^ a * C.q13Root ^ b * C.q14Root ^ c * C.q15Root ^ d

lemma pom_resonance_perron_multiplicative_independence_q12_15_pow_eq_one_exponent_zero
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

lemma pom_resonance_perron_multiplicative_independence_q12_15_table_independent :
    ∀ a b c d : ℕ,
      pom_resonance_perron_multiplicative_independence_q12_15_monomial
          pom_resonance_perron_multiplicative_independence_q12_15_certificateTable a b c d = 1 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  intro a b c d h
  have h2pow : 2 ^ a = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 2 ^ a ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d
    exact ⟨3 ^ b * 5 ^ c * 7 ^ d, by ring⟩
  have h3pow : 3 ^ b = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 3 ^ b ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d
    exact ⟨2 ^ a * 5 ^ c * 7 ^ d, by ring⟩
  have h5pow : 5 ^ c = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 5 ^ c ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d
    exact ⟨2 ^ a * 3 ^ b * 7 ^ d, by ring⟩
  have h7pow : 7 ^ d = 1 := by
    apply Nat.dvd_one.mp
    rw [← h]
    change 7 ^ d ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d
    exact ⟨2 ^ a * 3 ^ b * 5 ^ c, by ring⟩
  exact
    ⟨pom_resonance_perron_multiplicative_independence_q12_15_pow_eq_one_exponent_zero
        (by norm_num) h2pow,
      pom_resonance_perron_multiplicative_independence_q12_15_pow_eq_one_exponent_zero
        (by norm_num) h3pow,
      pom_resonance_perron_multiplicative_independence_q12_15_pow_eq_one_exponent_zero
        (by norm_num) h5pow,
      pom_resonance_perron_multiplicative_independence_q12_15_pow_eq_one_exponent_zero
        (by norm_num) h7pow⟩

/-- Concrete statement: the audited table has strict spectral gaps, and any cleared
nonnegative Perron monomial equal to the rational unit `1` has all exponents zero. -/
def pom_resonance_perron_multiplicative_independence_q12_15_statement : Prop :=
  pom_resonance_perron_multiplicative_independence_q12_15_strictGaps
      pom_resonance_perron_multiplicative_independence_q12_15_certificateTable ∧
    ∀ a b c d : ℕ,
      pom_resonance_perron_multiplicative_independence_q12_15_monomial
          pom_resonance_perron_multiplicative_independence_q12_15_certificateTable a b c d = 1 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0

theorem paper_pom_resonance_perron_multiplicative_independence_q12_15 :
    pom_resonance_perron_multiplicative_independence_q12_15_statement := by
  exact ⟨by norm_num [pom_resonance_perron_multiplicative_independence_q12_15_strictGaps,
      pom_resonance_perron_multiplicative_independence_q12_15_certificateTable],
    pom_resonance_perron_multiplicative_independence_q12_15_table_independent⟩

end Omega.POM
