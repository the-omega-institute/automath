import Mathlib.Data.Finsupp.Multiset
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Omega.GU.EllipticGateMinimalRegister
import Omega.GU.EllipticGatePrimeSpectrumClassification

namespace Omega.GU

/-- Model Fourier coefficient on the nonzero frequencies `± 2 m n`. -/
def ellipticGateLogSpeedFourierCoeffAtMultiple (c : ℚ) (n : ℕ) : ℚ :=
  if 0 < n then -(c ^ n) / (2 * n) else 0

/-- The sparse-support coefficient formula on multiples of `2m`. -/
theorem ellipticGateLogSpeedFourierCoeffAtMultiple_eq
    (c : ℚ) {n : ℕ} (hn : 0 < n) :
    ellipticGateLogSpeedFourierCoeffAtMultiple c n = -(c ^ n) / (2 * n) := by
  simp [ellipticGateLogSpeedFourierCoeffAtMultiple, hn]

/-- `p`-adic valuation identity for the coefficient on `2mn`. -/
theorem ellipticGateLogSpeedFourierCoeffAtMultiple_padicVal
    (c : ℚ) (hc0 : 0 < c) {n p : ℕ} (hp : Nat.Prime p) (hn : 0 < n) :
    padicValRat p (ellipticGateLogSpeedFourierCoeffAtMultiple c n) =
      (n : ℤ) * padicValRat p c - padicValRat p n - padicValRat p 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : c ≠ 0 := ne_of_gt hc0
  have hpow : c ^ n ≠ 0 := pow_ne_zero n hc
  have hnum : -(c ^ n) ≠ 0 := neg_ne_zero.mpr hpow
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hden : (2 * n : ℚ) ≠ 0 := by
    norm_num [hn.ne']
  have hmul :
      padicValRat p (2 * n : ℚ) = padicValRat p (2 : ℚ) + padicValRat p (n : ℚ) := by
    simpa using padicValRat.mul (p := p) (q := (2 : ℚ)) (r := (n : ℚ)) (by norm_num) hnq
  calc
    padicValRat p (ellipticGateLogSpeedFourierCoeffAtMultiple c n)
        = padicValRat p (-(c ^ n) / (2 * n : ℚ)) := by
            simp [ellipticGateLogSpeedFourierCoeffAtMultiple, hn]
    _ = padicValRat p (-(c ^ n)) - padicValRat p (2 * n : ℚ) := by
          rw [padicValRat.div hnum hden]
    _ = padicValRat p (c ^ n) - padicValRat p (2 * n : ℚ) := by
          rw [padicValRat.neg]
    _ = (n : ℤ) * padicValRat p c - padicValRat p (2 * n : ℚ) := by
          rw [padicValRat.pow hc]
    _ = (n : ℤ) * padicValRat p c - (padicValRat p (2 : ℚ) + padicValRat p (n : ℚ)) := by
          rw [hmul]
    _ = (n : ℤ) * padicValRat p c - padicValRat p n - padicValRat p 2 := by
          ring

/-- The witness frequencies `±2m` already recover the support gcd `2m`. -/
theorem ellipticGate_support_witness_gcd (m : ℕ) :
    Nat.gcd (Int.natAbs (((2 * m : ℕ) : ℤ))) (Int.natAbs (-((2 * m : ℕ) : ℤ))) = 2 * m := by
  have h1 : Int.natAbs (((2 * m : ℕ) : ℤ)) = 2 * m := by
    exact Int.natAbs_natCast (2 * m)
  have h2 : Int.natAbs (-((2 * m : ℕ) : ℤ)) = 2 * m := by
    rw [Int.natAbs_neg]
    exact Int.natAbs_natCast (2 * m)
  rw [h1, h2]
  exact Nat.gcd_self (2 * m)

/-- Any elliptic-gate realization of `Finset.range m` has the uniquely determined register size
`m`. -/
theorem ellipticGatePrimeSpectrum_range_rigidity
    {c : ℚ} {m m' : ℕ} (h : IsEllipticGatePrimeSpectrum c m' (Finset.range m)) :
    m' = m := by
  simpa using ellipticGatePrimeSpectrum_rigidity h

/-- Paper-facing rigidity package: the Fourier coefficients on multiples of `2m` have the sparse
closed form, their `p`-adic valuations split additively, the support gcd recovers `m`, and the
existing minimal-register and finite-spectrum classification wrappers pin down the register size.
    thm:group-jg-elliptic-gate-prime-spectrum-rigidity -/
theorem paper_group_jg_elliptic_gate_prime_spectrum_rigidity_package
    (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (m : ℕ) :
    let S := Finset.range m
    (∀ n : ℕ, 0 < n →
      ellipticGateLogSpeedFourierCoeffAtMultiple c n = -(c ^ n) / (2 * n)) ∧
      (∀ p n : ℕ, Nat.Prime p → 0 < n →
        padicValRat p (ellipticGateLogSpeedFourierCoeffAtMultiple c n) =
          (n : ℤ) * padicValRat p c - padicValRat p n - padicValRat p 2) ∧
      Nat.gcd (Int.natAbs (((2 * m : ℕ) : ℤ))) (Int.natAbs (-((2 * m : ℕ) : ℤ))) = 2 * m ∧
      m ≤ minimalRegisterSize c m ∧
      (∀ c' m', IsEllipticGatePrimeSpectrum c' m' S → m' = m) ∧
      ((∃ c' : ℚ, ∃ m' : ℕ, IsEllipticGatePrimeSpectrum c' m' S) ↔
        ∃ v : ℕ →₀ ℕ, ellipticGatePrimeSpectrum v = S) := by
  dsimp
  refine ⟨?_, ?_, ellipticGate_support_witness_gcd m, ?_, ?_, ?_⟩
  · intro n hn
    exact ellipticGateLogSpeedFourierCoeffAtMultiple_eq c hn
  · intro p n hp hn
    exact ellipticGateLogSpeedFourierCoeffAtMultiple_padicVal c hc0 hp hn
  · simpa using paper_group_jg_elliptic_gate_minimal_register c hc0 hc1 m
  · intro c' m' h
    exact ellipticGatePrimeSpectrum_range_rigidity h
  · simpa using paper_group_jg_elliptic_gate_prime_spectrum_classification (Finset.range m)

/-- Paper label wrapper for elliptic-gate prime-spectrum rigidity. -/
theorem paper_group_jg_elliptic_gate_prime_spectrum_rigidity
    (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (m : ℕ) :
    let S := Finset.range m
    (∀ n : ℕ, 0 < n →
      ellipticGateLogSpeedFourierCoeffAtMultiple c n = -(c ^ n) / (2 * n)) ∧
      (∀ p n : ℕ, Nat.Prime p → 0 < n →
        padicValRat p (ellipticGateLogSpeedFourierCoeffAtMultiple c n) =
          (n : ℤ) * padicValRat p c - padicValRat p n - padicValRat p 2) ∧
      Nat.gcd (Int.natAbs (((2 * m : ℕ) : ℤ))) (Int.natAbs (-((2 * m : ℕ) : ℤ))) = 2 * m ∧
      m ≤ minimalRegisterSize c m ∧
      (∀ c' m', IsEllipticGatePrimeSpectrum c' m' S → m' = m) ∧
      ((∃ c' : ℚ, ∃ m' : ℕ, IsEllipticGatePrimeSpectrum c' m' S) ↔
        ∃ v : ℕ →₀ ℕ, ellipticGatePrimeSpectrum v = S) :=
  paper_group_jg_elliptic_gate_prime_spectrum_rigidity_package c hc0 hc1 m

end Omega.GU
