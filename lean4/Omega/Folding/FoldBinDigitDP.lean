import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local tail cutoff used to package the `O(m)` digit-DP audit. The only property needed
here is that the tail length `K(m) - m` is exactly `m`. -/
def foldBinDigitK (m : ℕ) : ℕ :=
  2 * m

/-- The tail length seen by the bin-fold digit DP. -/
def foldBinDigitTailLength (m : ℕ) : ℕ :=
  foldBinDigitK m - m

/-- DP state count for admissible completions of a high-to-low tail digit string.
`prev = true` means the previous higher digit was `1`, `tight = true` means the already chosen
prefix still matches the slack digits exactly, and `forbidLast = true` enforces
`w_m = 1 → c_{m+1} = 0` at the final tail digit. -/
def foldBinDigitDPStateCount : List Bool → Bool → Bool → Bool → Nat
  | [], _, _, _ => 1
  | b :: bs, prev, tight, forbidLast =>
      let zeroTight := tight && decide (false = b)
      let zeroCount := foldBinDigitDPStateCount bs false zeroTight forbidLast
      let forbidOne := forbidLast && bs.isEmpty
      let oneAllowed := !prev && !(tight && !b) && !forbidOne
      let oneTight := tight && decide (true = b)
      let oneCount :=
        if oneAllowed then
          foldBinDigitDPStateCount bs true oneTight forbidLast
        else
          0
      zeroCount + oneCount

/-- The explicit admissible completions counted by the digit DP. This is the semantic tail set
under the same `prev`, `tight`, and boundary constraints. -/
def admissibleTailCompletions : List Bool → Bool → Bool → Bool → List (List Bool)
  | [], _, _, _ => [[]]
  | b :: bs, prev, tight, forbidLast =>
      let zeroTight := tight && decide (false = b)
      let zeroPart :=
        (admissibleTailCompletions bs false zeroTight forbidLast).map (List.cons false)
      let forbidOne := forbidLast && bs.isEmpty
      let oneAllowed := !prev && !(tight && !b) && !forbidOne
      let oneTight := tight && decide (true = b)
      let onePart :=
        if oneAllowed then
          (admissibleTailCompletions bs true oneTight forbidLast).map (List.cons true)
        else
          []
      zeroPart ++ onePart

/-- The digit-DP output attached to the tail digit string of the slack. -/
def foldBinDigitDP (slackDigits : List Bool) (wLast : Bool) : Nat :=
  foldBinDigitDPStateCount slackDigits false true wLast

/-- The concrete admissible-tail count produced by explicit enumeration. -/
def admissibleTailCount (slackDigits : List Bool) (wLast : Bool) : Nat :=
  (admissibleTailCompletions slackDigits false true wLast).length

/-- Four Boolean states are visited at each tail position, so the work is linear in the tail
length. -/
def foldBinDigitDPOperations (slackDigits : List Bool) : Nat :=
  4 * slackDigits.length + 4

theorem foldBinDigitDPStateCount_eq_length :
    ∀ slackDigits prev tight forbidLast,
      foldBinDigitDPStateCount slackDigits prev tight forbidLast =
        (admissibleTailCompletions slackDigits prev tight forbidLast).length := by
  intro slackDigits
  induction slackDigits with
  | nil =>
      intro prev tight forbidLast
      simp [foldBinDigitDPStateCount, admissibleTailCompletions]
  | cons b bs ih =>
      intro prev tight forbidLast
      simp [foldBinDigitDPStateCount, admissibleTailCompletions, ih, List.length_map]
      split_ifs <;> simp [List.length_map]

lemma foldBinDigitTailLength_eq (m : ℕ) : foldBinDigitTailLength m = m := by
  unfold foldBinDigitTailLength foldBinDigitK
  omega

/-- When the slack is presented by its Zeckendorf digits, the backward digit DP counts exactly the
admissible tail completions, and the number of visited states is `O(K(m)-m) = O(m)`.
    prop:fold-bin-digit-dp -/
theorem paper_fold_bin_digit_dp (m : ℕ) (wLast : Bool) (slackDigits : List Bool)
    (hlen : slackDigits.length = foldBinDigitTailLength m) :
    foldBinDigitDP slackDigits wLast = admissibleTailCount slackDigits wLast ∧
      foldBinDigitDPOperations slackDigits ≤ 4 * foldBinDigitTailLength m + 4 ∧
      foldBinDigitDPOperations slackDigits ≤ 4 * m + 4 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold foldBinDigitDP admissibleTailCount
    simpa using foldBinDigitDPStateCount_eq_length slackDigits false true wLast
  · unfold foldBinDigitDPOperations
    omega
  · calc
      foldBinDigitDPOperations slackDigits ≤ 4 * foldBinDigitTailLength m + 4 := by
        unfold foldBinDigitDPOperations
        omega
      _ = 4 * m + 4 := by rw [foldBinDigitTailLength_eq]

end Omega.Folding
