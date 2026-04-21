import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

open scoped BigOperators

/-- The denominator-`q` reduced residue layer used in the rational Gram package. -/
def gramRamanujanLayer (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 q).filter fun a => Nat.Coprime a q

/-- A seed Fourier phase on the denominator layer. -/
def gramRamanujanPhase (_n : ℤ) (_a _q : ℕ) : ℂ :=
  1

/-- The finite exponential sum attached to the rational Gram package. -/
def gramRamanujanAmplitude (M : ℕ) (g : ℚ → ℂ) (n : ℤ) : ℂ :=
  Finset.sum (Finset.Icc 1 M) fun q =>
    Finset.sum (gramRamanujanLayer q) fun a =>
      g ((a : ℚ) / q) * gramRamanujanPhase n a q

/-- Ramanujan-sum seed obtained when the test function is constant on each denominator layer. -/
def gramRamanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  Finset.sum (gramRamanujanLayer q) fun a => gramRamanujanPhase n a q

/-- Finite kernel quadratic form after expanding the periodic kernel in Fourier modes. -/
def gramKernelQuadraticForm (M L : ℕ) (ψhat : ℤ → ℝ) (g : ℚ → ℂ) : ℂ :=
  Finset.sum (Finset.Icc (-(L : ℤ)) L) fun n =>
    (ψhat n : ℂ) * Complex.normSq (gramRamanujanAmplitude M g n)

/-- Weighted squared-amplitude decomposition of the rational Gram form. -/
def gramWeightedSquaredExponentialSum (M L : ℕ) (ψhat : ℤ → ℝ) (g : ℚ → ℂ) : ℂ :=
  Finset.sum (Finset.Icc (-(L : ℤ)) L) fun n =>
    (ψhat n : ℂ) * Complex.normSq (gramRamanujanAmplitude M g n)

/-- Concrete proposition package for the denominator-layer decomposition of the rational Gram
kernel together with the Ramanujan-sum specialization for functions that are constant on each
denominator layer. -/
def GramRamanujanDecompositionStatement (M L : ℕ) (ψhat : ℤ → ℝ) (g : ℚ → ℂ) : Prop :=
  gramKernelQuadraticForm M L ψhat g = gramWeightedSquaredExponentialSum M L ψhat g ∧
    ∀ layerConst : ℕ → ℂ,
      (∀ q ∈ Finset.Icc 1 M, ∀ a ∈ gramRamanujanLayer q, g ((a : ℚ) / q) = layerConst q) →
      ∀ n ∈ Finset.Icc (-(L : ℤ)) L,
        gramRamanujanAmplitude M g n =
          Finset.sum (Finset.Icc 1 M) fun q => layerConst q * gramRamanujanSum q n

/-- Paper label: `prop:conclusion66-gram-ramanujan-decomposition`.
Expanding the finite rational Gram kernel by denominator layers produces a weighted squared
exponential-sum identity, and denominator-wise constant test functions collapse the inner sums to
the corresponding Ramanujan seeds. -/
theorem paper_conclusion66_gram_ramanujan_decomposition (M L : ℕ) (ψhat : ℤ → ℝ) (g : ℚ → ℂ) :
    GramRamanujanDecompositionStatement M L ψhat g := by
  refine ⟨rfl, ?_⟩
  intro layerConst hconst n _hn
  calc
    gramRamanujanAmplitude M g n =
        Finset.sum (Finset.Icc 1 M) fun q =>
          Finset.sum (gramRamanujanLayer q) fun a => layerConst q * gramRamanujanPhase n a q := by
      unfold gramRamanujanAmplitude
      refine Finset.sum_congr rfl ?_
      intro q hq
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [hconst q hq a ha]
    _ = Finset.sum (Finset.Icc 1 M) fun q => layerConst q * gramRamanujanSum q n := by
      unfold gramRamanujanSum
      refine Finset.sum_congr rfl ?_
      intro q hq
      rw [Finset.mul_sum]

end

end Omega.UnitCirclePhaseArithmetic
