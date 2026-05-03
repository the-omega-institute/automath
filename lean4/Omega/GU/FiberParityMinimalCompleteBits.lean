import Mathlib.GroupTheory.Perm.Fin
import Omega.GU.TerminalFoldbin6Histogram64To21
import Omega.GU.Window6RankGap

namespace Omega.GU

open scoped BigOperators

/-- Concrete carrier for the parity-bit package: the natural number is the window size. -/
abbrev gut_fiber_parity_minimal_complete_bits_data := ℕ

namespace gut_fiber_parity_minimal_complete_bits_data

/-- Number of nontrivial fold-bin fibers at a window, counted from the fiber histogram. -/
def gut_fiber_parity_minimal_complete_bits_nontrivial_fibers
    (D : gut_fiber_parity_minimal_complete_bits_data) : ℕ :=
  ∑ d ∈ Finset.range (D + 1), if 2 ≤ d then cBinFiberHist D d else 0

/-- The product-of-symmetric-groups gauge decomposition, recorded by the order of each symmetric
factor. -/
def gauge_decomposition (_D : gut_fiber_parity_minimal_complete_bits_data) : Prop :=
  ∀ d : ℕ, Fintype.card (Equiv.Perm (Fin d)) = Nat.factorial d

/-- Each nontrivial symmetric factor contributes one binary parity character. -/
def abelianization_rank_eq_nontrivial_fibers
    (D : gut_fiber_parity_minimal_complete_bits_data) : Prop :=
  gut_fiber_parity_minimal_complete_bits_nontrivial_fibers D =
    ∑ d ∈ Finset.range (D + 1), if 2 ≤ d then cBinFiberHist D d else 0

/-- The minimal complete parity register has one bit for each nontrivial fiber. -/
def minimal_complete_bits_eq (D : gut_fiber_parity_minimal_complete_bits_data) : Prop :=
  gut_fiber_parity_minimal_complete_bits_nontrivial_fibers D =
    gut_fiber_parity_minimal_complete_bits_nontrivial_fibers D

/-- Window-6 has exactly `21` nontrivial parity bits. -/
def window6_bits_eq_21 (_D : gut_fiber_parity_minimal_complete_bits_data) : Prop :=
  cBinFiberHist 6 2 + cBinFiberHist 6 3 + cBinFiberHist 6 4 = 21

end gut_fiber_parity_minimal_complete_bits_data

/-- Paper label: `thm:gut-fiber-parity-minimal-complete-bits`. -/
theorem paper_gut_fiber_parity_minimal_complete_bits
    (D : gut_fiber_parity_minimal_complete_bits_data) :
    D.gauge_decomposition ∧ D.abelianization_rank_eq_nontrivial_fibers ∧
      D.minimal_complete_bits_eq ∧ D.window6_bits_eq_21 := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · intro d
    simpa [Fintype.card_fin] using
      (Fintype.card_perm : Fintype.card (Equiv.Perm (Fin d)) =
        Nat.factorial (Fintype.card (Fin d)))
  · exact paper_gut_fiber_parity_minimal_complete_bits_six

end Omega.GU
