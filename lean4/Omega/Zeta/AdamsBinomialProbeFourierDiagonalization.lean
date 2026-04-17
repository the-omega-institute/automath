import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The centered binomial index `N + m` used in the Adams probe Fourier coefficients. -/
def adamsBinomialProbeCenteredIndex (N : ℕ) (m : ℤ) : ℕ :=
  Int.toNat (m + N)

/-- The closed-form Fourier coefficient of the order-`N` Adams binomial probe. -/
def adamsBinomialProbeFourierCoeff (N d : ℕ) (c : ℤ → ℂ) (m : ℤ) : ℂ :=
  if _hm : m ∈ Finset.Icc (-(N : ℤ)) N then
    ((-1 : ℂ) ^ Int.natAbs m) * (((4 : ℂ) ^ N)⁻¹) *
      (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ) * c (-(d : ℤ) * m)
  else
    0

/-- The Fourier-diagonalized Adams binomial probe series on a phase `ω`. -/
def adamsBinomialProbeFourierSeries (N d : ℕ) (c : ℤ → ℂ) (ω : ℂˣ) : ℂ :=
  Finset.sum (Finset.Icc (-(N : ℤ)) N)
    (fun m => adamsBinomialProbeFourierCoeff N d c m * ((ω : ℂ) ^ m))

private lemma centeredIndex_le_double (N : ℕ) {m : ℤ} (hm : m ∈ Finset.Icc (-(N : ℤ)) N) :
    adamsBinomialProbeCenteredIndex N m ≤ 2 * N := by
  rcases Finset.mem_Icc.mp hm with ⟨hlo, hhi⟩
  have hnonneg : 0 ≤ m + N := by linarith
  have hupper : m + N ≤ 2 * N := by linarith
  simpa [adamsBinomialProbeCenteredIndex, Int.toNat_of_nonneg hnonneg] using hupper

private lemma centeredChoose_ne_zero (N : ℕ) {m : ℤ} (hm : m ∈ Finset.Icc (-(N : ℤ)) N) :
    (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ) ≠ 0 := by
  norm_num [Nat.cast_eq_zero]
  exact Nat.choose_ne_zero (centeredIndex_le_double N hm)

theorem paper_xi_adams_binomial_probe_fourier_diagonalization (N d : ℕ) (c : ℤ → ℂ) :
    (∀ ω : ℂˣ,
      adamsBinomialProbeFourierSeries N d c ω =
        Finset.sum (Finset.Icc (-(N : ℤ)) N) fun m =>
          (((-1 : ℂ) ^ Int.natAbs m) * (((4 : ℂ) ^ N)⁻¹) *
            (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ) *
            c (-(d : ℤ) * m)) * ((ω : ℂ) ^ m)) ∧
      (∀ m : ℤ, m ∈ Finset.Icc (-(N : ℤ)) N →
        adamsBinomialProbeFourierCoeff N d c m =
          ((-1 : ℂ) ^ Int.natAbs m) * (((4 : ℂ) ^ N)⁻¹) *
            (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ) * c (-(d : ℤ) * m)) ∧
      (∀ m : ℤ, m ∈ Finset.Icc (-(N : ℤ)) N →
        c (-(d : ℤ) * m) =
          ((-1 : ℂ) ^ Int.natAbs m) * (((4 : ℂ) ^ N) /
            (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ)) *
              adamsBinomialProbeFourierCoeff N d c m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp [adamsBinomialProbeFourierCoeff, hm]
  · intro m hm
    simp [adamsBinomialProbeFourierCoeff, hm]
  · intro m hm
    have hchoose := centeredChoose_ne_zero N hm
    have hfour : ((4 : ℂ) ^ N) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    have hcoeff :
        adamsBinomialProbeFourierCoeff N d c m =
          ((-1 : ℂ) ^ Int.natAbs m) * (((4 : ℂ) ^ N)⁻¹) *
            (Nat.choose (2 * N) (adamsBinomialProbeCenteredIndex N m) : ℂ) * c (-(d : ℤ) * m) := by
      simp [adamsBinomialProbeFourierCoeff, hm]
    rw [hcoeff]
    field_simp [hchoose, hfour]
    have hsign2 : (((-1 : ℂ) ^ m.natAbs) ^ 2) = 1 := by
      rcases neg_one_pow_eq_or ℂ m.natAbs with h | h <;> simp [h]
    rw [hsign2, mul_one]

end

end Omega.Zeta
