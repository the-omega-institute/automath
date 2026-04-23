import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete coefficient data for the real-input-40 prime generating-function identity. The
fields record the three primitive coefficient sequences together with the low-degree corrections
and the parity/`4`-divisibility splitting law for all `n ≥ 3`. -/
structure real_input_40_prime_genfun_identity_data where
  pM : ℕ → ℤ
  pB : ℕ → ℤ
  pF : ℕ → ℤ
  pF_one : pF 1 = 1
  low_one : pM 1 - pB 1 = 0
  low_two : pM 2 - pB 2 = 1 + pF 2 + pF 1
  prime_split :
    ∀ n : ℕ,
      3 ≤ n →
        pM n - pB n = (-1 : ℤ) ^ n * pF n + if n % 4 = 2 then pF (n / 2) else 0

/-- Coefficient of the explicit `z + z²` correction term. -/
def real_input_40_prime_genfun_identity_z_correction_coeff (n : ℕ) : ℤ :=
  (if n = 1 then 1 else 0) + if n = 2 then 1 else 0

/-- Coefficient of the `P_F(-z)` contribution. -/
def real_input_40_prime_genfun_identity_pF_neg_coeff (pF : ℕ → ℤ) (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * pF n

/-- Coefficient of `(P_F(z²) - P_F(-z²)) / 2`, expressed without division by using the
`n ≡ 2 [MOD 4]` case split from the paper proof. -/
def real_input_40_prime_genfun_identity_half_difference_coeff (pF : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n % 4 = 2 then pF (n / 2) else 0

/-- Coefficientwise form of
`z + z^2 + P_F(-z) + (P_F(z^2) - P_F(-z^2)) / 2`. -/
def real_input_40_prime_genfun_identity_rhs_coeff (pF : ℕ → ℤ) (n : ℕ) : ℤ :=
  real_input_40_prime_genfun_identity_z_correction_coeff n +
    real_input_40_prime_genfun_identity_pF_neg_coeff pF n +
      real_input_40_prime_genfun_identity_half_difference_coeff pF n

namespace real_input_40_prime_genfun_identity_data

/-- Paper-facing coefficientwise version of the generating-function identity
`P_M(z) - P_B(z) = z + z² + P_F(-z) + (P_F(z²) - P_F(-z²))/2`. -/
def statement (D : real_input_40_prime_genfun_identity_data) : Prop :=
  ∀ n : ℕ,
    1 ≤ n →
    D.pM n - D.pB n = real_input_40_prime_genfun_identity_rhs_coeff D.pF n

end real_input_40_prime_genfun_identity_data

/-- Paper label: `cor:real-input-40-prime-genfun-identity`. The coefficientwise parity law for
`p_n(M) - p_n(B)`, together with the low-degree values at `n = 1, 2`, packages exactly into the
closed generating-function identity
`P_M(z) - P_B(z) = z + z² + P_F(-z) + (P_F(z²) - P_F(-z²)) / 2`. -/
theorem paper_real_input_40_prime_genfun_identity
    (D : real_input_40_prime_genfun_identity_data) : D.statement := by
  intro n hn1
  by_cases h1 : n = 1
  · subst h1
    simpa [real_input_40_prime_genfun_identity_rhs_coeff,
      real_input_40_prime_genfun_identity_z_correction_coeff,
      real_input_40_prime_genfun_identity_pF_neg_coeff,
      real_input_40_prime_genfun_identity_half_difference_coeff, D.pF_one] using D.low_one
  · by_cases h2 : n = 2
    · subst h2
      simpa [real_input_40_prime_genfun_identity_rhs_coeff,
        real_input_40_prime_genfun_identity_z_correction_coeff,
        real_input_40_prime_genfun_identity_pF_neg_coeff,
        real_input_40_prime_genfun_identity_half_difference_coeff, D.pF_one,
        add_assoc, add_left_comm, add_comm] using D.low_two
    · have hn : 3 ≤ n := by omega
      simpa [real_input_40_prime_genfun_identity_rhs_coeff,
        real_input_40_prime_genfun_identity_z_correction_coeff,
        real_input_40_prime_genfun_identity_pF_neg_coeff,
        real_input_40_prime_genfun_identity_half_difference_coeff, h1, h2] using
        D.prime_split n hn

end Omega.SyncKernelRealInput
