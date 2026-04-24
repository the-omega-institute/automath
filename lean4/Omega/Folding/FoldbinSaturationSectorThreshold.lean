import Mathlib.Tactic
import Omega.Folding.FiberArithmeticProperties
import Omega.Folding.FoldBinDigitDP
import Omega.Folding.FoldBinFiberTail

namespace Omega.Folding

/-- The threshold slack contributed by the largest admissible tail in the concrete digit-DP model.
The tail length is `K(m) - m = m`, so the Fibonacci count `F_{L+2}` supplies the saturation
envelope. -/
def foldbinSMax (m : ℕ) : ℕ :=
  Nat.fib (foldBinDigitTailLength m + 2) - 1

/-- The sector where the bin-fold combinatorial upper bound can saturate: the final visible bit is
`0`, so the boundary obstruction disappears, and the stable value leaves enough slack to accommodate
the maximal admissible tail. -/
def foldbinSaturationSector (m : ℕ) : Set (Omega.X m) :=
  {w | Omega.get w.1 (m - 1) = false ∧ Omega.stableValue w + foldbinSMax m ≤ 2 ^ m - 1}

/-- Membership in the saturation sector is the concrete threshold test used in the paper. -/
def foldbinSaturatesUpperBound (m : ℕ) (w : Omega.X m) : Prop :=
  w ∈ foldbinSaturationSector m

/-- Paper-facing threshold characterization of the saturation sector: the concrete test is exactly
the conjunction `w_m = 0` and enough slack for the maximal tail, the all-zero stable word shows
nonemptiness exactly when the global slack is nonnegative, and the two complementary obstructions
(`w_m = 1` or insufficient slack) force strict inequality.
    thm:foldbin-saturation-sector-threshold -/
theorem paper_foldbin_saturation_sector_threshold (m : ℕ) (_hm : 2 ≤ m) :
    (∀ w : Omega.X m, foldbinSaturatesUpperBound m w ↔
      Omega.get w.1 (m - 1) = false ∧ Omega.stableValue w + foldbinSMax m ≤ 2 ^ m - 1) ∧
    (Set.Nonempty (foldbinSaturationSector m) ↔ foldbinSMax m ≤ 2 ^ m - 1) ∧
    (∀ w : Omega.X m, Omega.get w.1 (m - 1) = true → ¬ foldbinSaturatesUpperBound m w) ∧
    (∀ w : Omega.X m, 2 ^ m - 1 < Omega.stableValue w + foldbinSMax m →
      ¬ foldbinSaturatesUpperBound m w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    rfl
  · constructor
    · rintro ⟨w, hw⟩
      exact le_trans (Nat.le_add_left _ _) hw.2
    · intro hS
      refine ⟨⟨fun _ => false, Omega.no11_allFalse⟩, ?_⟩
      constructor
      · by_cases h : m - 1 < m <;> simp [Omega.get, h]
      · simpa using hS
  · intro w hwLast hSat
    simpa [hwLast] using hSat.1
  · intro w hwSlack hSat
    exact not_lt_of_ge hSat.2 hwSlack

end Omega.Folding
