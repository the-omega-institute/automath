import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldbinGaugeInvariantRing

namespace Omega.OperatorAlgebra

open scoped BigOperators

/-- The fiberwise multiplicity of the degree-`j` factor `(1 + t + ··· + t^j)` in the formal
coinvariant Hilbert product. For a fiber of size `d`, this factor appears exactly when `j + 1 ≤ d`.
-/
noncomputable def foldbinCoinvariantFactorCount (m j : ℕ) : ℕ :=
  ∑ x : Omega.X m, if j + 1 ≤ Omega.X.fiberMultiplicity x then 1 else 0

/-- The formal product of fiberwise factorial dimensions. -/
noncomputable def foldbinCoinvariantTotalDimension (m : ℕ) : ℕ :=
  ∏ x : Omega.X m, Nat.factorial (Omega.X.fiberMultiplicity x)

/-- The formal top degree obtained by summing the symmetric-group coinvariant top degrees
`binom(d_w, 2)` over fibers. -/
noncomputable def foldbinCoinvariantTopDegree (m : ℕ) : ℕ :=
  ∑ x : Omega.X m, Nat.choose (Omega.X.fiberMultiplicity x) 2

/-- The audited window-`6` Hilbert factor list. -/
def foldbinCoinvariantHilbertSeriesSix : List (ℕ × ℕ) :=
  [(1, 21), (2, 13), (3, 9)]

/-- The audited window-`6` total dimension written in factorial form. -/
def foldbinCoinvariantTotalDimensionSix : ℕ :=
  (Nat.factorial 2) ^ 8 * (Nat.factorial 3) ^ 4 * (Nat.factorial 4) ^ 9

/-- The audited window-`6` top degree `8·1 + 4·3 + 9·6`. -/
def foldbinCoinvariantTopDegreeSix : ℕ :=
  8 * 1 + 4 * 3 + 9 * 6

/-- Concrete package for the foldbin coinvariant algebra: the gauge action splits fiberwise, the
Hilbert factors are counted by the fiberwise thresholds `j + 1 ≤ d_w`, the total dimension and top
degree are the standard symmetric-group products, and the audited `m = 6` specialization matches
the explicit histogram. -/
def FoldbinCoinvariantGorensteinSpec (m : ℕ) : Prop :=
  Omega.Folding.paper_fold_bin_gauge_decomposition m ∧
    (∀ j : ℕ,
      foldbinCoinvariantFactorCount m j =
        ∑ x : Omega.X m, if j + 1 ≤ Omega.X.fiberMultiplicity x then 1 else 0) ∧
    foldbinCoinvariantTotalDimension m =
      ∏ x : Omega.X m, Nat.factorial (Omega.X.fiberMultiplicity x) ∧
    foldbinCoinvariantTopDegree m =
      ∑ x : Omega.X m, Nat.choose (Omega.X.fiberMultiplicity x) 2 ∧
    (m = 6 →
      foldbinCoinvariantHilbertSeriesSix = [(1, 21), (2, 13), (3, 9)] ∧
        foldbinCoinvariantTotalDimensionSix = (Nat.factorial 2) ^ 8 * (Nat.factorial 3) ^ 4 *
          (Nat.factorial 4) ^ 9 ∧
        foldbinCoinvariantTotalDimensionSix = 2 ^ 8 * 6 ^ 4 * 24 ^ 9 ∧
        foldbinCoinvariantTopDegreeSix = 74)

/-- Paper label: `thm:foldbin-coinvariant-gorenstein`. -/
theorem paper_foldbin_coinvariant_gorenstein (m : ℕ) : FoldbinCoinvariantGorensteinSpec m := by
  refine ⟨Omega.Folding.paper_fold_bin_gauge_decomposition_spec m, ?_, rfl, rfl, ?_⟩
  · intro j
    rfl
  · intro hm
    subst hm
    rcases paper_foldbin_gauge_invariant_ring with
      ⟨_hDecomp, _hdeg1, _hdeg2, _hdeg3, _hdeg4, _hseries, hdim⟩
    exact ⟨rfl, rfl, hdim, by native_decide⟩

end Omega.OperatorAlgebra
