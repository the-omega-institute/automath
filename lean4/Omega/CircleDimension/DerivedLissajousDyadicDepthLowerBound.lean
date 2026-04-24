import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Omega.CircleDimension.DerivedLissajousExactHistogramDyadicThreshold

/-- A deterministic `L`-bit reader can realize at most `2^L` visible buckets, so any injective
restriction to a maximal Lissajous fiber forces the dyadic depth lower bound.
    cor:derived-lissajous-dyadic-depth-lower-bound -/
theorem paper_derived_lissajous_dyadic_depth_lower_bound (a b L : ℕ)
    (reader : Fin (Omega.CircleDimension.lissajousMaxFiber a b) → Fin (2 ^ L))
    (hreader : Function.Injective reader) :
    Omega.CircleDimension.lissajousMaxFiber a b ≤ 2 ^ L ∧
      Omega.CircleDimension.lissajousDyadicThreshold a b ≤ L := by
  have hcard : Omega.CircleDimension.lissajousMaxFiber a b ≤ 2 ^ L := by
    simpa using Fintype.card_le_of_injective reader hreader
  have hdepth : Nat.clog 2 (Omega.CircleDimension.lissajousMaxFiber a b) ≤ L := by
    exact (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 hcard
  exact ⟨hcard, by simpa [Omega.CircleDimension.lissajousDyadicThreshold] using hdepth⟩
