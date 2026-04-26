import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete certificate package for the Fibonacci product collision. -/
structure conclusion_fiber_multiplicity_product_noninjective_data where
  conclusion_fiber_multiplicity_product_noninjective_certificate : Unit := ()

namespace conclusion_fiber_multiplicity_product_noninjective_data

/-- Fibonacci product statistic on a finite list encoding a finite multiset of path lengths. -/
def conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
    (lengths : List ℕ) : ℕ :=
  (lengths.map fun ell => Nat.fib (ell + 2)).prod

/-- The singleton spectrum `{4}`. -/
def conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum : List ℕ :=
  [4]

/-- The triple spectrum `{1, 1, 1}`. -/
def conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum : List ℕ :=
  [1, 1, 1]

/-- The explicit product collision `F_6 = F_3^3`. -/
def productCollision (_D : conclusion_fiber_multiplicity_product_noninjective_data) : Prop :=
  conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum =
    conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
      conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum ∧
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum ≠
        conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum

/-- The Fibonacci product statistic is not injective on finite spectra. -/
def noninjective (_D : conclusion_fiber_multiplicity_product_noninjective_data) : Prop :=
  ∃ A B : List ℕ,
    A ≠ B ∧
      conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct A =
        conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct B

/-- Equal product multiplicity can identify spectra with different internal graph sizes. -/
def losesGraphType (_D : conclusion_fiber_multiplicity_product_noninjective_data) : Prop :=
  ∃ A B : List ℕ,
    A ≠ B ∧
      conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct A =
        conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct B ∧
      A.length ≠ B.length

end conclusion_fiber_multiplicity_product_noninjective_data

open conclusion_fiber_multiplicity_product_noninjective_data

/-- Paper label: `prop:conclusion-fiber-multiplicity-product-noninjective`. -/
theorem paper_conclusion_fiber_multiplicity_product_noninjective
    (D : conclusion_fiber_multiplicity_product_noninjective_data) :
    D.productCollision ∧ D.noninjective ∧ D.losesGraphType := by
  have hcollision :
      conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
          conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum =
        conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct
          conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum := by
    norm_num [conclusion_fiber_multiplicity_product_noninjective_fibonacciProduct,
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum,
      conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum, Nat.fib]
  have hne :
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum ≠
        conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum := by
    decide
  refine ⟨⟨hcollision, hne⟩, ?_, ?_⟩
  · exact ⟨
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum,
      conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum,
      hne, hcollision⟩
  · refine ⟨
      conclusion_fiber_multiplicity_product_noninjective_singletonSpectrum,
      conclusion_fiber_multiplicity_product_noninjective_tripleOneSpectrum,
      hne, hcollision, ?_⟩
    decide

end Omega.Conclusion
