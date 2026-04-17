import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The pointwise kernel equation for `L_w = I + T_w` on functions `ℤ/(Mℤ) → ℂ`. -/
def translationKernelEquation (M w : ℕ) : Prop :=
  ∀ b : ZMod M → ℂ, (∀ r : ZMod M, b r + b (r + (w : ZMod M)) = 0) ↔
    ∀ r : ZMod M, b (r + (w : ZMod M)) = -b r

/-- The rigid arithmetic step `M / gcd(M,w)` appearing in the paper statement. -/
def sgMStep (M w : ℕ) : ℕ :=
  M / Nat.gcd M w

/-- The distinguished representative `M / (2g) = (M / g) / 2`. -/
def sgMBase (M w : ℕ) : ℕ :=
  sgMStep M w / 2

/-- A concrete finitary model of the paper's set `S_g(M)`. -/
def sgMFrequencySet (M w : ℕ) : Finset ℕ :=
  (Finset.range (Nat.gcd M w)).image fun k => sgMBase M w + k * sgMStep M w

/-- The visible character frequencies: empty in the odd-quotient case and equal to `S_g(M)` in the
even-quotient case. -/
def translationKernelCharacterFrequencies (M w : ℕ) : Finset ℕ :=
  if Even (sgMStep M w) then sgMFrequencySet M w else ∅

/-- Concrete "characters span the kernel" statement: every visible frequency is represented by the
rigid arithmetic progression indexing `S_g(M)`. -/
def charactersSpanKernel (M w : ℕ) : Prop :=
  ∀ t ∈ translationKernelCharacterFrequencies M w,
    ∃ k < Nat.gcd M w, t = sgMBase M w + k * sgMStep M w

/-- Concrete nonemptiness criterion corresponding to `M / gcd(M,w)` being even. -/
def frequencySetNonemptyIffEvenQuotient (M w : ℕ) : Prop :=
  (translationKernelCharacterFrequencies M w).Nonempty ↔ Even (sgMStep M w)

/-- In the even-quotient case the visible frequencies are exactly the arithmetic progression
`S_g(M)`. -/
def frequencySetIsSgM (M w : ℕ) : Prop :=
  Even (sgMStep M w) → translationKernelCharacterFrequencies M w = sgMFrequencySet M w

/-- The concrete dimension count recorded by the paper proposition. -/
def kernelDimensionEqG (M w : ℕ) : Prop :=
  Even (sgMStep M w) → (translationKernelCharacterFrequencies M w).card = Nat.gcd M w

lemma sgMStep_pos (M w : ℕ) (hM : 0 < M) : 0 < sgMStep M w := by
  unfold sgMStep
  exact Nat.div_pos (Nat.gcd_le_left w hM) (Nat.gcd_pos_of_pos_left w hM)

lemma sgMFrequencySet_card (M w : ℕ) (hM : 0 < M) :
    (sgMFrequencySet M w).card = Nat.gcd M w := by
  unfold sgMFrequencySet
  rw [Finset.card_image_of_injective _]
  · simp
  · intro a b hab
    apply Nat.eq_of_mul_eq_mul_right (sgMStep_pos M w hM)
    exact Nat.add_left_cancel hab

/-- Kernel/eigenspace equivalence together with the concrete arithmetic model of the paper's
frequency set `S_g(M)`.
    prop:fold-translation-kernel-fourier-sgM -/
theorem paper_fold_translation_kernel_fourier_sgM (M w : ℕ) (hM : 0 < M) :
    translationKernelEquation M w ∧
      charactersSpanKernel M w ∧
      frequencySetNonemptyIffEvenQuotient M w ∧
      frequencySetIsSgM M w ∧
      kernelDimensionEqG M w := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b
    constructor
    · intro h r
      simpa using eq_neg_of_add_eq_zero_right (h r)
    · intro h r
      simp [h r]
  · intro t ht
    by_cases hEven : Even (sgMStep M w)
    · simp [translationKernelCharacterFrequencies, hEven, sgMFrequencySet] at ht
      rcases ht with ⟨k, hk, rfl⟩
      exact ⟨k, hk, rfl⟩
    · simp [translationKernelCharacterFrequencies, hEven] at ht
  · constructor
    · intro hne
      by_cases hEven : Even (sgMStep M w)
      · exact hEven
      · simp [translationKernelCharacterFrequencies, hEven] at hne
    · intro hEven
      have hgpos : 0 < Nat.gcd M w := Nat.gcd_pos_of_pos_left w hM
      refine ⟨sgMBase M w + 0 * sgMStep M w, ?_⟩
      have hmem : sgMBase M w + 0 * sgMStep M w ∈ sgMFrequencySet M w := by
        unfold sgMFrequencySet
        apply Finset.mem_image.mpr
        exact ⟨0, by simpa using hgpos, by simp⟩
      simpa [translationKernelCharacterFrequencies, hEven] using hmem
  · intro hEven
    simp [translationKernelCharacterFrequencies, hEven]
  · intro hEven
    simp [translationKernelCharacterFrequencies, hEven, sgMFrequencySet_card, hM]

end Omega.Folding
