import Mathlib.Tactic
import Omega.Folding.Killo2adicHolographicAttractorDimension

namespace Omega.Folding

/-- Paper label: `cor:killo-2adic-holographic-ambient-dimension-zero`. Specializing the general
`B`-adic attractor theorem to `B = 2^L` yields the dimension formula and the zero-measure branch
for `q < 2^L`. -/
theorem paper_killo_2adic_holographic_ambient_dimension_zero {L q : ℕ} (hL : 0 < L)
    (hq : 0 < q) (hqB : q ≤ 2 ^ L) (hqLt : q < 2 ^ L) :
    killo_2adic_holographic_attractor_dimension_value (2 ^ L) q = Real.logb (2 ^ L) q ∧
      killo_2adic_holographic_attractor_dimension_haarMeasure (2 ^ L) q = 0 := by
  have hB : 1 < 2 ^ L := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL) with ⟨k, rfl⟩
    have hpow_pos : 0 < 2 ^ k := by positivity
    omega
  rcases
      paper_killo_2adic_holographic_attractor_dimension (B := 2 ^ L) (q := q) hB hq hqB with
    ⟨_, _, hdim, hhaar_zero, _⟩
  refine ⟨?_, hhaar_zero hqLt⟩
  simpa using hdim

end Omega.Folding
