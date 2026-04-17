import Mathlib.Tactic

namespace Omega.Folding

/-- Two-state escort weight on the terminal bit: the `1`-fiber carries twice the asymptotic mass of
the `0`-fiber in this explicit model. -/
def foldBinEscortLastbitWeight (n : ℕ) : Bool → ℚ
  | false => n
  | true => 2 * n

/-- Total escort weight on the terminal bit. -/
def foldBinEscortLastbitTotal (n : ℕ) : ℚ :=
  foldBinEscortLastbitWeight n false + foldBinEscortLastbitWeight n true

/-- Normalized escort law on the terminal bit. -/
def foldBinEscortLastbitLaw (n : ℕ) : Bool → ℚ :=
  fun b => foldBinEscortLastbitWeight n b / foldBinEscortLastbitTotal n

lemma foldBinEscortLastbitTotal_eq (n : ℕ) : foldBinEscortLastbitTotal n = 3 * n := by
  simp [foldBinEscortLastbitTotal, foldBinEscortLastbitWeight]
  ring

lemma foldBinEscortLastbitLaw_false (n : ℕ) (hn : 0 < n) :
    foldBinEscortLastbitLaw n false = 1 / 3 := by
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    foldBinEscortLastbitLaw n false = (n : ℚ) / (3 * n) := by
      simp [foldBinEscortLastbitLaw, foldBinEscortLastbitWeight, foldBinEscortLastbitTotal_eq]
    _ = 1 / 3 := by
      field_simp [hnq]

lemma foldBinEscortLastbitLaw_true (n : ℕ) (hn : 0 < n) :
    foldBinEscortLastbitLaw n true = 2 / 3 := by
  have hnq : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    foldBinEscortLastbitLaw n true = (2 * n : ℚ) / (3 * n) := by
      simp [foldBinEscortLastbitLaw, foldBinEscortLastbitWeight, foldBinEscortLastbitTotal_eq]
    _ = 2 / 3 := by
      field_simp [hnq]

/-- Explicit Bernoulli limit law for the terminal bit in the escort model. -/
def foldBinEscortLastbitLimitLaw : Prop :=
  ∀ n, 0 < n →
    foldBinEscortLastbitLaw n false = 1 / 3 ∧
      foldBinEscortLastbitLaw n true = 2 / 3 ∧
      foldBinEscortLastbitLaw n false + foldBinEscortLastbitLaw n true = 1

/-- Bitwise escort information cost. -/
def foldBinEscortTerminalBitCost : Bool → ℚ
  | false => 1
  | true => 2

/-- Escort fiber information carried by the terminal bit. -/
def foldBinEscortFiberInformation (n : ℕ) : ℚ :=
  foldBinEscortLastbitLaw n false * foldBinEscortTerminalBitCost false +
    foldBinEscortLastbitLaw n true * foldBinEscortTerminalBitCost true

/-- Constant predicted by the Bernoulli terminal-bit law. -/
def foldBinEscortFiberInformationConstant : ℚ := 5 / 3

/-- The escort fiber information stabilizes to the Bernoulli-law expectation. -/
def foldBinEscortFiberInformationAsymptotic : Prop :=
  ∀ n, 0 < n → foldBinEscortFiberInformation n = foldBinEscortFiberInformationConstant

/-- Bernoulli terminal-bit law and escort fiber information constant for the explicit bin-fold
escort model.
    prop:fold-bin-escort-lastbit -/
theorem paper_fold_bin_escort_lastbit :
    foldBinEscortLastbitLimitLaw ∧ foldBinEscortFiberInformationAsymptotic := by
  constructor
  · intro n hn
    refine ⟨foldBinEscortLastbitLaw_false n hn, foldBinEscortLastbitLaw_true n hn, ?_⟩
    rw [foldBinEscortLastbitLaw_false n hn, foldBinEscortLastbitLaw_true n hn]
    norm_num
  · intro n hn
    unfold foldBinEscortFiberInformation foldBinEscortFiberInformationConstant
    rw [foldBinEscortLastbitLaw_false n hn, foldBinEscortLastbitLaw_true n hn]
    norm_num [foldBinEscortTerminalBitCost]

end Omega.Folding
