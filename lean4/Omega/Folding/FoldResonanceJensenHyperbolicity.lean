import Mathlib.Algebra.Polynomial.Basic
import Omega.Folding.FoldCosineProductEntireRenormalizationZeros

namespace Omega.Folding

open scoped BigOperators
open fold_resonance_entire_lp_data

noncomputable section

/-- Concrete Jensen polynomial proxy built from the first `N` shifted odd resonance zeros. -/
def fold_resonance_jensen_hyperbolicity_jensen_polynomial (d N : ℕ) : Polynomial ℝ :=
  ∏ i : Fin N, (Polynomial.X - Polynomial.C (fold_resonance_entire_lp_odd_zero (d + i)))

/-- Hyperbolicity is recorded by an explicit factorization into real linear terms. -/
def fold_resonance_jensen_hyperbolicity_hyperbolic (d N : ℕ) : Prop :=
  ∃ roots : Fin N → ℝ,
    fold_resonance_jensen_hyperbolicity_jensen_polynomial d N =
      ∏ i : Fin N, (Polynomial.X - Polynomial.C (roots i))

/-- The fold-resonance entire witness lies in the recorded LP package, and every shifted finite
Jensen truncation written from its explicit real zero lattice is hyperbolic. -/
def fold_resonance_jensen_hyperbolicity_statement : Prop :=
  let D := fold_cosine_product_entire_renormalization_zeros_explicit_data
  D.has_entire_extension ∧
    D.has_self_similarity ∧
    D.has_explicit_real_zeros ∧
    ∀ d N : ℕ, fold_resonance_jensen_hyperbolicity_hyperbolic d N

/-- Paper label: `cor:fold-resonance-jensen-hyperbolicity`. The existing fold-resonance LP witness
supplies the entire/self-similar real-zero package, and the associated finite Jensen truncations
split completely over `ℝ` into the recorded linear factors. -/
theorem paper_fold_resonance_jensen_hyperbolicity :
    fold_resonance_jensen_hyperbolicity_statement := by
  have hres := paper_fold_cosine_product_entire_renormalization_zeros
  refine ⟨hres.2.1, hres.2.2.1, hres.2.2.2.1, ?_⟩
  intro d N
  refine ⟨fun i => fold_resonance_entire_lp_odd_zero (d + i), rfl⟩

end

end Omega.Folding
