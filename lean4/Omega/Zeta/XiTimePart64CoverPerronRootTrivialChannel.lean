import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix
open scoped BigOperators

/-- Concrete nonnegative norm proxy for the Perron radius of a single channel block. -/
def xi_time_part64_cover_perron_root_trivial_channel_blockRadius {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℕ) : ℕ :=
  ∑ i, ∑ j, A i j

/-- Cover radius obtained by taking the maximal channel radius across a finite block-diagonal cover.
The trivial character is represented by the distinguished channel `0`. -/
def xi_time_part64_cover_perron_root_trivial_channel_coverRadius {κ n : ℕ}
    (blocks : Fin (κ + 1) → Matrix (Fin n) (Fin n) ℕ) : ℕ :=
  Finset.univ.sup fun χ =>
    xi_time_part64_cover_perron_root_trivial_channel_blockRadius (blocks χ)

/-- `thm:xi-time-part64-cover-perron-root-trivial-channel`

For a finite cover operator whose twisted channel blocks are all bounded by the trivial block in the
chosen Collatz-Wielandt norm proxy, the full cover radius is realized by the trivial channel. -/
theorem paper_xi_time_part64_cover_perron_root_trivial_channel
    {κ n : ℕ} (blocks : Fin (κ + 1) → Matrix (Fin n) (Fin n) ℕ)
    (hdom : ∀ χ,
      xi_time_part64_cover_perron_root_trivial_channel_blockRadius (blocks χ) ≤
        xi_time_part64_cover_perron_root_trivial_channel_blockRadius (blocks 0)) :
    xi_time_part64_cover_perron_root_trivial_channel_coverRadius blocks =
      xi_time_part64_cover_perron_root_trivial_channel_blockRadius (blocks 0) := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro χ hχ
    exact hdom χ
  · simpa [xi_time_part64_cover_perron_root_trivial_channel_coverRadius] using
      (Finset.le_sup
        (s := Finset.univ)
        (f := fun χ =>
          xi_time_part64_cover_perron_root_trivial_channel_blockRadius (blocks χ))
        (by simp : (0 : Fin (κ + 1)) ∈ Finset.univ))

end Omega.Zeta
