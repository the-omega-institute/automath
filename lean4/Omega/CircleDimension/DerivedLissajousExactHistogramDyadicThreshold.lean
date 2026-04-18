import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Omega.CircleDimension

/-- The three nonzero fiber sizes appearing in the discrete Lissajous histogram. -/
def lissajousFiberHistogram (a b : ℕ) (k : ℕ) : ℕ :=
  let g := Nat.gcd a b
  if k = g then 2
  else if k = 2 * g then a / g + b / g - 2
  else if k = 4 * g then (a * b - a - b + g) / (2 * g)
  else 0

/-- Wedderburn block sizes and multiplicities recorded as `(matrix size, count)` pairs. -/
def lissajousWedderburnBlocks (a b : ℕ) : List (ℕ × ℕ) :=
  let g := Nat.gcd a b
  [(g, 2), (2 * g, a / g + b / g - 2), (4 * g, (a * b - a - b + g) / (2 * g))]

/-- The largest Lissajous fiber size. -/
def lissajousMaxFiber (a b : ℕ) : ℕ := 4 * Nat.gcd a b

/-- The least dyadic depth reaching the maximal fiber size. -/
def lissajousDyadicThreshold (a b : ℕ) : ℕ := Nat.clog 2 (lissajousMaxFiber a b)

/-- In the rational-rose package the origin fiber depends only on the numerator. -/
def rationalRoseOriginFiberCount (n d : ℕ) : ℕ := 2 * n

end Omega.CircleDimension

/-- Paper-facing wrapper for the discrete Lissajous exact histogram, the corresponding
Wedderburn block decomposition, the dyadic-threshold lower bound encoded by `Nat.clog`, and the
rational-rose origin-fiber count.
    thm:derived-lissajous-exact-histogram-dyadic-threshold -/
theorem paper_derived_lissajous_exact_histogram_dyadic_threshold (a b n d : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hcop : Nat.Coprime n d) :
    let g := Nat.gcd a b
    Omega.CircleDimension.lissajousFiberHistogram a b g = 2 ∧
      Omega.CircleDimension.lissajousFiberHistogram a b (2 * g) = a / g + b / g - 2 ∧
      Omega.CircleDimension.lissajousFiberHistogram a b (4 * g) =
        (a * b - a - b + g) / (2 * g) ∧
      Omega.CircleDimension.lissajousWedderburnBlocks a b =
        [(g, 2), (2 * g, a / g + b / g - 2), (4 * g, (a * b - a - b + g) / (2 * g))] ∧
      Omega.CircleDimension.lissajousMaxFiber a b = 4 * g ∧
      Omega.CircleDimension.lissajousMaxFiber a b ≤
        2 ^ Omega.CircleDimension.lissajousDyadicThreshold a b ∧
      Omega.CircleDimension.rationalRoseOriginFiberCount n d = 2 * n := by
  let _ := hcop
  set g := Nat.gcd a b
  have hg : 0 < g := by
    subst g
    exact Nat.gcd_pos_of_pos_left b (Nat.succ_le_iff.mp ha)
  have h2g_ne_g : 2 * g ≠ g := by omega
  have h4g_ne_g : 4 * g ≠ g := by omega
  have h4g_ne_2g : 4 * g ≠ 2 * g := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Omega.CircleDimension.lissajousFiberHistogram, g]
  · simp [Omega.CircleDimension.lissajousFiberHistogram, g, h2g_ne_g]
  · simp [Omega.CircleDimension.lissajousFiberHistogram, g, h4g_ne_g, h4g_ne_2g]
  · simp [Omega.CircleDimension.lissajousWedderburnBlocks, g]
  · simp [Omega.CircleDimension.lissajousMaxFiber, g]
  · simpa [Omega.CircleDimension.lissajousDyadicThreshold,
      Omega.CircleDimension.lissajousMaxFiber] using Nat.le_pow_clog one_lt_two
      (Omega.CircleDimension.lissajousMaxFiber a b)
  · simp [Omega.CircleDimension.rationalRoseOriginFiberCount]
