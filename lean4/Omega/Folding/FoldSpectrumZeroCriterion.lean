import Omega.Folding.FoldSpectrumFactorization

open scoped BigOperators

namespace Omega.Folding

/-- The normalized fold spectrum vanishes exactly when one cosine factor in the coordinatewise
factorization vanishes.
    thm:fold-spectrum-zero-criterion -/
theorem paper_fold_spectrum_zero_criterion {n : Nat} (w : Fin n -> Real) (theta : Real) :
    normalizedResidueProfileFourier w theta = 0 <->
      Exists fun i => Real.cos (w i * theta) = 0 := by
  rcases paper_fold_spectrum_factorization w theta with ⟨_, hnormalized, _⟩
  rw [hnormalized, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    unfold residueProfileCosFactor at hi
    exact ⟨i, Complex.ofReal_eq_zero.mp hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    unfold residueProfileCosFactor
    exact Complex.ofReal_eq_zero.mpr hi

end Omega.Folding
