import Mathlib

namespace Omega.Folding

noncomputable section

/-- Concrete two-point centered fold data. The centered residues occur in the reciprocal pair
`±a`, so every odd contribution cancels termwise. -/
structure FoldCenteredOddMomentsData where
  amplitude : ℝ
  weight : ℝ

namespace FoldCenteredOddMomentsData

def centeredOddMoment (D : FoldCenteredOddMomentsData) (n : ℕ) : ℝ :=
  D.weight * D.amplitude ^ n + D.weight * (-D.amplitude) ^ n

def centeredCharacteristic (D : FoldCenteredOddMomentsData) (t : ℝ) : ℝ :=
  D.weight * Real.cos (t * D.amplitude) + D.weight * Real.cos (t * (-D.amplitude))

def centeredOddCumulant (D : FoldCenteredOddMomentsData) (n : ℕ) : ℝ :=
  D.centeredOddMoment n / (n + 1)

def oddMomentsVanish (D : FoldCenteredOddMomentsData) : Prop :=
  ∀ n, Odd n → D.centeredOddMoment n = 0

def characteristicFunctionEven (D : FoldCenteredOddMomentsData) : Prop :=
  ∀ t : ℝ, D.centeredCharacteristic (-t) = D.centeredCharacteristic t

def oddCumulantsVanish (D : FoldCenteredOddMomentsData) : Prop :=
  ∀ n, Odd n → D.centeredOddCumulant n = 0

lemma neg_amplitude_pow_of_odd (D : FoldCenteredOddMomentsData) {n : ℕ} (hn : Odd n) :
    (-D.amplitude) ^ n = -(D.amplitude ^ n) := by
  rw [neg_eq_neg_one_mul, mul_pow, hn.neg_one_pow]
  ring

end FoldCenteredOddMomentsData

open FoldCenteredOddMomentsData

/-- Centered odd moments vanish by pairing the reciprocal residues `±a`, the centered
characteristic function is even, and the odd cumulants vanish with the same symmetry.
    cor:derived-fold-centered-odd-moments-vanish -/
theorem paper_derived_fold_centered_odd_moments_vanish (D : FoldCenteredOddMomentsData) :
    D.oddMomentsVanish ∧ D.characteristicFunctionEven ∧ D.oddCumulantsVanish := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [FoldCenteredOddMomentsData.centeredOddMoment, D.neg_amplitude_pow_of_odd hn]
    ring
  · intro t
    simp [FoldCenteredOddMomentsData.centeredCharacteristic, Real.cos_neg]
  · intro n hn
    have hmoment : D.centeredOddMoment n = 0 := by
      rw [FoldCenteredOddMomentsData.centeredOddMoment, D.neg_amplitude_pow_of_odd hn]
      ring
    rw [FoldCenteredOddMomentsData.centeredOddCumulant, hmoment]
    ring

end
end Omega.Folding
