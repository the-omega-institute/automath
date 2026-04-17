import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic

namespace Omega.GU

/-- Concrete data for the binomial Fourier extraction identity. The moment is defined by the
finite Laurent expansion appearing in the paper statement. -/
structure JGBinomialFilteringData where
  r : Complex
  fourierCoeff : Int → Complex

/-- The pushed-forward holomorphic moments are encoded by the explicit binomial/Fourier sum. -/
noncomputable def JGBinomialFilteringData.moment (D : JGBinomialFilteringData) (n : Nat) :
    Complex :=
  Finset.sum (Finset.range (n + 1)) fun j =>
    (Nat.choose n j : Complex) * D.r ^ (2 * j) / D.r ^ n *
      D.fourierCoeff (((2 * j : Nat) : Int) - (n : Int))

/-- Paper label: `thm:group-jg-binomial-filtering-fourier-extraction`. -/
theorem paper_group_jg_binomial_filtering_fourier_extraction
    (D : JGBinomialFilteringData) (n : Nat) :
    D.moment n =
      Finset.sum (Finset.range (n + 1)) (fun j =>
        (Nat.choose n j : Complex) * D.r ^ (2 * j) / D.r ^ n *
          D.fourierCoeff (((2 * j : Nat) : Int) - (n : Int))) := by
  rfl

end Omega.GU
