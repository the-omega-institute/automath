import Mathlib
import Omega.Zeta.AdamsBinomialProbeFourierDiagonalization

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The lazy-walk heat kernel extracted from the Adams binomial coefficients. -/
def adamsBinomialProbeLazyWalkHeatKernel (N : ℕ) (m : ℤ) : ℂ :=
  if m ∈ Finset.Icc (-(N : ℤ)) N then
    (((4 : ℂ) ^ N)⁻¹) * (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ)
  else
    0

/-- The signed observable paired with the lazy-walk heat kernel. -/
def adamsBinomialProbeLazyWalkObservable (d : ℕ) (c : ℤ → ℂ) (ω : ℂˣ) (m : ℤ) : ℂ :=
  ((-1 : ℂ) ^ Int.natAbs m) * c (-(d : ℤ) * m) * ((ω : ℂ) ^ m)

/-- The Adams binomial probe written as a finite expectation against the lazy-walk heat kernel. -/
def adamsBinomialProbeLazyWalkExpectation (N d : ℕ) (c : ℤ → ℂ) (ω : ℂˣ) : ℂ :=
  Finset.sum (Finset.Icc (-(N : ℤ)) N) fun m =>
    adamsBinomialProbeLazyWalkHeatKernel N m * adamsBinomialProbeLazyWalkObservable d c ω m

/-- The Fourier-diagonalized Adams binomial probe can be rewritten as a finite expectation against
the lazy-walk heat kernel, with the individual Fourier coefficients given by the same kernel times
the signed probe observable. `cor:xi-adams-binomial-probe-lazy-walk-heat-kernel` -/
theorem paper_xi_adams_binomial_probe_lazy_walk_heat_kernel (N d : ℕ) (c : ℤ → ℂ) :
    (∀ ω : ℂˣ,
      adamsBinomialProbeFourierSeries N d c ω =
        adamsBinomialProbeLazyWalkExpectation N d c ω) ∧
      (∀ m : ℤ,
        adamsBinomialProbeFourierCoeff N d c m =
          ((-1 : ℂ) ^ Int.natAbs m) * adamsBinomialProbeLazyWalkHeatKernel N m *
            c (-(d : ℤ) * m)) := by
  have hdiag := paper_xi_adams_binomial_probe_fourier_diagonalization N d c
  refine ⟨?_, ?_⟩
  · intro ω
    calc
      adamsBinomialProbeFourierSeries N d c ω =
          Finset.sum (Finset.Icc (-(N : ℤ)) N) fun m =>
            (((-1 : ℂ) ^ Int.natAbs m) * (((4 : ℂ) ^ N)⁻¹) *
              (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ) *
              c (-(d : ℤ) * m)) * ((ω : ℂ) ^ m) := hdiag.1 ω
      _ = adamsBinomialProbeLazyWalkExpectation N d c ω := by
        unfold adamsBinomialProbeLazyWalkExpectation
        refine Finset.sum_congr rfl ?_
        intro m hm
        simp [adamsBinomialProbeLazyWalkHeatKernel, adamsBinomialProbeLazyWalkObservable, hm,
          mul_assoc, mul_comm]
  · intro m
    by_cases hm : m ∈ Finset.Icc (-(N : ℤ)) N
    · rw [hdiag.2.1 m hm]
      simp [adamsBinomialProbeLazyWalkHeatKernel, hm, mul_assoc, mul_comm]
    · simp [adamsBinomialProbeFourierCoeff, adamsBinomialProbeLazyWalkHeatKernel, hm,
        mul_comm]

end

end Omega.Zeta
