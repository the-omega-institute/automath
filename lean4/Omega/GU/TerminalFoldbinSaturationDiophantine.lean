import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Combinatorics.FibonacciCube
import Omega.GU.Window6SaturationMaxfiberCanonicalXL

namespace Omega.GU

noncomputable instance instFintypeFoldbinZeroFiber (m : Nat) : Fintype (foldbin_zero_fiber m) := by
  delta foldbin_zero_fiber
  infer_instance

/-- The terminal alternating-tail residue left after the saturated foldbin cutoff. Since
`K(m) = m`, only the parity of the hidden tail survives: even tails contribute `0`, odd tails
contribute `1`. -/
def terminalFoldbinAlternatingTailCutoff (m : Nat) : Nat :=
  if Even m then 0 else 1

/-- Paper-facing saturation/Diophantine wrapper: at the explicit cutoff `K(m) = m` the residual
zero fiber collapses to the unique length-`0` stable word, and the alternating-tail residue is the
parity split `0/1`. For `m ≥ 2` that residue is bounded by `2^m - 1`, so saturation is
equivalent to the advertised Diophantine inequality.
    thm:terminal-foldbin-saturation-diophantine -/
theorem paper_terminal_foldbin_saturation_diophantine (m : Nat) (hm : 2 ≤ m) :
    Fintype.card (foldbin_zero_fiber m) = 1 ∧
      terminalFoldbinAlternatingTailCutoff m ≤ 2 ^ m - 1 ∧
      (saturation_point m ↔ terminalFoldbinAlternatingTailCutoff m ≤ 2 ^ m - 1) := by
  have hs : saturation_point m := by
    simp [saturation_point, K]
  have hcard : Fintype.card (foldbin_zero_fiber m) = 1 := by
    calc
      Fintype.card (foldbin_zero_fiber m) = Fintype.card (Omega.X (K m - m)) := by
        exact Fintype.card_congr (paper_window6_saturation_maxfiber_canonical_xl m hs)
      _ = 1 := by
        simp [K]
  have hcutoff : terminalFoldbinAlternatingTailCutoff m ≤ 2 ^ m - 1 := by
    by_cases hEven : Even m
    · simp [terminalFoldbinAlternatingTailCutoff, hEven]
    · have hmaxlt : Omega.X.maxFiberMultiplicity m < 2 ^ m :=
        Omega.maxFiber_lt_wordcount m hm
      have hmaxpos : 1 ≤ Omega.X.maxFiberMultiplicity m :=
        Nat.succ_le_of_lt (Omega.X.maxFiberMultiplicity_pos m)
      have hone : 1 ≤ 2 ^ m - 1 := by
        omega
      simpa [terminalFoldbinAlternatingTailCutoff, hEven] using hone
  refine ⟨hcard, hcutoff, ?_⟩
  constructor
  · intro _
    exact hcutoff
  · intro _
    exact hs

end Omega.GU
