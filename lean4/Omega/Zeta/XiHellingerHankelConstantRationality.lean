import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- The explicit rational closed form used for the even Hellinger moments. -/
def xiHellingerEvenMomentClosedForm (n : ℕ) : ℚ :=
  (Nat.factorial (2 * n) : ℚ) / ((2 : ℚ) ^ (2 * n) * (n + 1))

/-- The Hellinger moment sequence: odd moments vanish, and even moments are given by the explicit
rational closed form above. -/
def xiHellingerMoment (m : ℕ) : ℚ :=
  if Even m then xiHellingerEvenMomentClosedForm (m / 2) else 0

/-- Odd Hellinger moments vanish. -/
def xiHellingerOddMomentsVanish : Prop :=
  ∀ n : ℕ, xiHellingerMoment (2 * n + 1) = 0

/-- Even Hellinger moments are given by the explicit closed form. -/
def xiHellingerEvenMomentsClosedForm : Prop :=
  ∀ n : ℕ, xiHellingerMoment (2 * n) = xiHellingerEvenMomentClosedForm n

/-- The `κ × κ` Hankel matrix built from the Hellinger moments. -/
def xiHellingerHankelMatrix (κ : ℕ) : Matrix (Fin κ) (Fin κ) ℚ :=
  fun i j => xiHellingerMoment (i.1 + j.1)

/-- The associated Hankel constant. -/
def xiHellingerHankelConstant (κ : ℕ) : ℚ :=
  (xiHellingerHankelMatrix κ).det

/-- Since every matrix entry is rational, so is the Hankel determinant. -/
def xiHellingerHankelConstantIsRational (κ : ℕ) : Prop :=
  ∃ q : ℚ, xiHellingerHankelConstant κ = q

/-- The odd moments vanish by evenness, the even moments match their explicit rational formula,
and the resulting Hankel determinant is rational.
    prop:xi-hellinger-hankel-constant-rationality -/
theorem paper_xi_hellinger_hankel_constant_rationality (κ : ℕ) :
    xiHellingerOddMomentsVanish ∧ xiHellingerEvenMomentsClosedForm ∧
      xiHellingerHankelConstantIsRational κ := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hodd : Odd (2 * n + 1) := ⟨n, by ring⟩
    have hnot : ¬ Even (2 * n + 1) := Nat.not_even_iff_odd.mpr hodd
    simp [xiHellingerMoment, hnot]
  · intro n
    have heven : Even (2 * n) := ⟨n, by ring⟩
    have hdiv : (2 * n) / 2 = n := by
      simpa [Nat.mul_comm] using (Nat.mul_div_right n 2)
    simpa [xiHellingerMoment, heven, hdiv]
  · exact ⟨xiHellingerHankelConstant κ, rfl⟩

end Omega.Zeta
