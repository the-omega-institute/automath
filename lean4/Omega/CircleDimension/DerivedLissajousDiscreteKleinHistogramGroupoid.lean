import Mathlib.Tactic
import Omega.CircleDimension.DerivedLissajousExactHistogramDyadicThreshold

namespace Omega.CircleDimension

/-- The center dimension of the discrete Lissajous groupoid algebra, recorded as the total number
of Wedderburn blocks. -/
def lissajousCenterDimension (a b : ℕ) : ℕ :=
  (lissajousWedderburnBlocks a b).map Prod.snd |>.sum

private lemma lissajousFiberHistogram_support (a b k : ℕ)
    (hk : lissajousFiberHistogram a b k ≠ 0) :
    k = Nat.gcd a b ∨ k = 2 * Nat.gcd a b ∨ k = 4 * Nat.gcd a b := by
  set g := Nat.gcd a b
  by_cases hg : k = g
  · exact Or.inl hg
  · by_cases h2g : k = 2 * g
    · exact Or.inr <| Or.inl h2g
    · by_cases h4g : k = 4 * g
      · exact Or.inr <| Or.inr h4g
      · exfalso
        have hzero : lissajousFiberHistogram a b k = 0 := by
          simp [lissajousFiberHistogram, g, hg, h2g, h4g]
        exact hk hzero

/-- Paper label: `prop:derived-lissajous-discrete-klein-histogram-groupoid`. The existing exact
histogram theorem already gives the three allowed fiber sizes and the Wedderburn block list; this
wrapper adds the support classification and the resulting center-dimension count. -/
theorem paper_derived_lissajous_discrete_klein_histogram_groupoid (a b : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) :
    let g := Nat.gcd a b
    lissajousFiberHistogram a b g = 2 ∧
      lissajousFiberHistogram a b (2 * g) = a / g + b / g - 2 ∧
      lissajousFiberHistogram a b (4 * g) = (a * b - a - b + g) / (2 * g) ∧
      (∀ k, lissajousFiberHistogram a b k ≠ 0 → k = g ∨ k = 2 * g ∨ k = 4 * g) ∧
      lissajousWedderburnBlocks a b =
        [(g, 2), (2 * g, a / g + b / g - 2), (4 * g, (a * b - a - b + g) / (2 * g))] ∧
      lissajousCenterDimension a b =
        2 + (a / g + b / g - 2) + (a * b - a - b + g) / (2 * g) := by
  have hbase :=
    paper_derived_lissajous_exact_histogram_dyadic_threshold a b 1 1 ha hb (by decide)
  set g := Nat.gcd a b
  rcases hbase with ⟨hg, h2g, h4g, hblocks, -, -, -⟩
  refine ⟨hg, h2g, h4g, ?_, hblocks, ?_⟩
  · intro k hk
    simpa [g] using lissajousFiberHistogram_support a b k hk
  · simp [lissajousCenterDimension, hblocks]
    omega

end Omega.CircleDimension
