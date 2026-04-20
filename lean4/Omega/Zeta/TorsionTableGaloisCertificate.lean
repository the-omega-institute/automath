import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Omega.Zeta.TorsionTableGaloisCovariance

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The normalized Fourier kernel used in the local torsion-table certificate. -/
def torsionTableFourierKernel (j n : ℕ) : ℂ :=
  (ω_q ^ j) ^ n

/-- The normalized discrete Fourier coefficient built from one torsion-table layer. -/
def torsionTableFourierCoeff (q : ℕ) (y : ℕ → ℂ) (n : ℕ) : ℂ :=
  (q : ℂ)⁻¹ * Finset.sum (Finset.range q) (fun j => y j * torsionTableFourierKernel j n)

/-- In the chapter-local normalization, the torsion table itself is the only nontrivial source of
Galois variation in the Fourier coefficient formula. -/
def torsionTableCoefficientwiseGaloisInvariant (q : ℕ) (y : ℕ → ℂ) : Prop :=
  ∀ h : ℕ, ∀ j : ℕ, j < q → σ_h (y j) = y j

/-- Transport the Fourier coefficient formula by the chapter-local Galois action. -/
def torsionTableFourierCoeffGaloisTransport (q : ℕ) (y : ℕ → ℂ) (n : ℕ) (_h : ℕ) : ℂ :=
  (q : ℂ)⁻¹ *
    Finset.sum (Finset.range q) (fun j => σ_h (y j) * σ_h (torsionTableFourierKernel j n))

private theorem torsionTableFourierKernel_galois_fixed (q _h j n : ℕ) (hq : 2 ≤ q) :
    σ_h (torsionTableFourierKernel j n) = torsionTableFourierKernel j n := by
  have hcov :=
    paper_finite_part_torsion_table_galois_covariance q hq (fun z => z ^ n) 0 j
  simp [torsionTableFourierKernel, ω_q, σ_h] at hcov ⊢

/-- A torsion table whose entries are fixed coefficientwise by the chapter-local Galois action
produces Fourier coefficients satisfying the same local Galois transport law; under the current
normalization `ω_q = 1` and `σ_h = id`, so the check is coefficientwise.
    cor:finite-part-torsion-table-galois-certificate -/
theorem paper_finite_part_torsion_table_galois_certificate
    (q : ℕ) (hq : 2 ≤ q) (y : ℕ → ℂ)
    (hy : torsionTableCoefficientwiseGaloisInvariant q y) :
    ∀ n h,
      torsionTableFourierCoeffGaloisTransport q y n h = torsionTableFourierCoeff q y n := by
  intro n h
  unfold torsionTableFourierCoeffGaloisTransport torsionTableFourierCoeff
  refine congrArg ((q : ℂ)⁻¹ * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hyj : σ_h (y j) = y j := hy h j (Finset.mem_range.mp hj)
  have hkernel : σ_h (torsionTableFourierKernel j n) = torsionTableFourierKernel j n :=
    torsionTableFourierKernel_galois_fixed q h j n hq
  simp [hyj, hkernel]

end

end Omega.Zeta
