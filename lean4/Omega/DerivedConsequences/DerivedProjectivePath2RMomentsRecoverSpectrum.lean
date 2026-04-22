import Omega.POM.ProjectivePathAtomicPronyRank
import Mathlib.Tactic

namespace Omega.DerivedConsequences

open scoped BigOperators

/-- First-`2r`-moment recovery package for the fixed-length projective-path atomic spectrum: the
moments are the Vandermonde sums, the truncated Hankel matrix agrees with the Vandermonde Gram
factorization, and the existing Prony theorem records the recovered rank, recurrence order, and
annihilating polynomial. -/
def derived_projective_path_2r_moments_recover_spectrum_statement
    (D : Omega.POM.ProjectivePathAtomicPronyData) : Prop :=
  (∀ q : ℕ, q < 2 * D.atomCount →
    Omega.POM.projectivePathMoment D q =
      ∑ a : Fin D.atomCount,
        (D.multiplicity a : ℤ) * Omega.POM.projectivePathVandermondeEntry D q a) ∧
    (∀ i j : ℕ, i + j < 2 * D.atomCount →
      Omega.POM.projectivePathHankelEntry D i j =
        Omega.POM.projectivePathVandermondeGramEntry D i j) ∧
    Omega.POM.projectivePathHankelRank D = D.atomCount ∧
    Omega.POM.projectivePathMinimalRecurrenceOrder D = D.atomCount ∧
    Omega.POM.projectivePathMinimalRecurrencePolynomial D =
      Omega.POM.projectivePathAnnihilatingPolynomial D

/-- Paper label: `cor:derived-projective-path-2r-moments-recover-spectrum`. The first `2r`
moments already furnish the Vandermonde/Hankel data used by the atomic Prony theorem, so the
rank, minimal recurrence order, and annihilating polynomial are the recovered spectral
certificate. -/
theorem paper_derived_projective_path_2r_moments_recover_spectrum
    (D : Omega.POM.ProjectivePathAtomicPronyData) :
    derived_projective_path_2r_moments_recover_spectrum_statement D := by
  rcases Omega.POM.paper_derived_projective_path_atomic_prony_rank D with
    ⟨hGram, hRank, hOrder, hPoly⟩
  refine ⟨?_, ?_, hRank, hOrder, hPoly⟩
  · intro q hq
    simp [Omega.POM.projectivePathMoment, Omega.POM.projectivePathVandermondeEntry]
  · intro i j hij
    exact hGram i j

end Omega.DerivedConsequences
