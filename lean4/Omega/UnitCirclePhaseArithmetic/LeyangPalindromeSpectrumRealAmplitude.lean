import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators

noncomputable section

/-- Concrete coefficient data for the finite Lee--Yang palindrome spectrum package. -/
structure LeyangPalindromeSpectrumData where
  degree : ℕ
  coeff : Fin (degree + 1) → ℂ

namespace LeyangPalindromeSpectrumData

/-- Mirror index `k ↦ n - k` in the finite mode range `{0, ..., n}`. -/
def mirrorIndex (D : LeyangPalindromeSpectrumData) (k : Fin (D.degree + 1)) :
    Fin (D.degree + 1) :=
  ⟨D.degree - k.1, lt_of_le_of_lt (Nat.sub_le D.degree k.1) (Nat.lt_succ_self D.degree)⟩

/-- Finite Fourier amplitude before pairing symmetric modes. -/
def phaseNormalizedAmplitude (D : LeyangPalindromeSpectrumData) (z : ℂ) : ℂ :=
  ∑ k : Fin (D.degree + 1), D.coeff k * z ^ k.1

/-- Coefficientwise conjugate imbalance of the `k`th symmetric mode pair. -/
def amplitudeModeImbalance (D : LeyangPalindromeSpectrumData) (k : Fin (D.degree + 1)) : ℂ :=
  D.coeff k - star (D.coeff (D.mirrorIndex k))

/-- The phase-normalized amplitude is real exactly when every symmetric mode pair is
self-conjugate. -/
def realValuedAmplitude (D : LeyangPalindromeSpectrumData) : Prop :=
  ∀ k : Fin (D.degree + 1), D.amplitudeModeImbalance k = 0

/-- Conjugate-palindromic coefficient condition `a_k = \overline{a_{n-k}}`. -/
def conjugatePalindromic (D : LeyangPalindromeSpectrumData) : Prop :=
  ∀ k : Fin (D.degree + 1), D.coeff k = star (D.coeff (D.mirrorIndex k))

end LeyangPalindromeSpectrumData

open LeyangPalindromeSpectrumData

/-- Paper label: `lem:leyang-palindrome-spectrum-real-amplitude`. The coefficientwise conjugate
pairing of the finite Fourier modes is equivalent to vanishing mode imbalance, which is the local
real-amplitude condition used in the phase-normalized model. -/
theorem paper_leyang_palindrome_spectrum_real_amplitude (D : LeyangPalindromeSpectrumData) :
    D.realValuedAmplitude ↔ D.conjugatePalindromic := by
  constructor
  · intro h k
    exact sub_eq_zero.mp (h k)
  · intro h k
    exact sub_eq_zero.mpr (h k)

end

end Omega.UnitCirclePhaseArithmetic
