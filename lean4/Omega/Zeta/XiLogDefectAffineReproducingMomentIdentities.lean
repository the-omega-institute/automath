import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.XiLogdefectBandpassPoissonRepresentation

open scoped BigOperators

namespace Omega.Zeta

/-- The lower endpoint of the unit-width band centered at height `1`. -/
def xiLogdefectAffineBandLower (δ : ℝ) : ℝ :=
  1 - δ

/-- The upper endpoint of the unit-width band centered at height `1`. -/
def xiLogdefectAffineBandUpper (δ : ℝ) : ℝ :=
  1 + δ

/-- The single-defect affine log-defect kernel. -/
noncomputable def xiLogdefectAffineKernel (γ δ x : ℝ) : ℝ :=
  xiLogdefectBandpassScalar x γ (xiLogdefectAffineBandLower δ) (xiLogdefectAffineBandUpper δ)

/-- The same kernel written as a Poisson-primitive difference. -/
noncomputable def xiLogdefectAffinePoissonKernel (γ δ x : ℝ) : ℝ :=
  xiLogdefectPoissonPrimitive x γ (xiLogdefectAffineBandUpper δ) -
    xiLogdefectPoissonPrimitive x γ (xiLogdefectAffineBandLower δ)

/-- Symbolic zeroth moment of the affine log-defect kernel. -/
noncomputable def xiLogdefectAffineZerothMoment (_γ δ : ℝ) : ℝ :=
  Real.pi * (xiLogdefectAffineBandUpper δ - xiLogdefectAffineBandLower δ)

/-- Symbolic first moment of the affine log-defect kernel. -/
noncomputable def xiLogdefectAffineFirstMoment (γ δ : ℝ) : ℝ :=
  γ * xiLogdefectAffineZerothMoment γ δ

/-- Symbolic affine moment of the affine log-defect kernel. -/
noncomputable def xiLogdefectAffineMoment (γ δ a b : ℝ) : ℝ :=
  a * xiLogdefectAffineFirstMoment γ δ + b * xiLogdefectAffineZerothMoment γ δ

/-- Finite superposition of affine log-defect kernels. -/
noncomputable def xiLogdefectFinitePotential {n : ℕ}
    (x : ℝ) (center radius mass : Fin n → ℝ) : ℝ :=
  ∑ i, mass i * xiLogdefectAffineKernel (center i) (radius i) x

/-- Finite superposition of the Poisson-primitive form. -/
noncomputable def xiLogdefectFinitePoissonPotential {n : ℕ}
    (x : ℝ) (center radius mass : Fin n → ℝ) : ℝ :=
  ∑ i, mass i * xiLogdefectAffinePoissonKernel (center i) (radius i) x

/-- Finite zeroth-moment functional. -/
noncomputable def xiLogdefectFiniteZerothMoment {n : ℕ} (center radius mass : Fin n → ℝ) : ℝ :=
  ∑ i, mass i * xiLogdefectAffineZerothMoment (center i) (radius i)

/-- Finite first-moment functional. -/
noncomputable def xiLogdefectFiniteFirstMoment {n : ℕ} (center radius mass : Fin n → ℝ) : ℝ :=
  ∑ i, mass i * xiLogdefectAffineFirstMoment (center i) (radius i)

/-- Finite affine-moment functional. -/
noncomputable def xiLogdefectFiniteAffineMoment {n : ℕ}
    (center radius mass : Fin n → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, mass i * xiLogdefectAffineMoment (center i) (radius i) a b

/-- Paper label: `thm:xi-logdefect-affine-reproducing-moment-identities`. -/
theorem paper_xi_logdefect_affine_reproducing_moment_identities :
    (∀ γ δ, 0 < δ → δ ≤ 1 / 2 →
      ∀ x, xiLogdefectAffineKernel γ δ x = xiLogdefectAffinePoissonKernel γ δ x) ∧
    (∀ γ δ, xiLogdefectAffineZerothMoment γ δ = 2 * Real.pi * δ) ∧
    (∀ γ δ, xiLogdefectAffineFirstMoment γ δ = 2 * Real.pi * δ * γ) ∧
    (∀ γ δ a b, xiLogdefectAffineMoment γ δ a b = 2 * Real.pi * δ * (a * γ + b)) ∧
    (∀ {n : ℕ} (center radius mass : Fin n → ℝ),
      (∀ i, 0 < radius i) → (∀ i, radius i ≤ 1 / 2) →
      ∀ x, xiLogdefectFinitePotential x center radius mass =
        xiLogdefectFinitePoissonPotential x center radius mass) ∧
    (∀ {n : ℕ} (center radius mass : Fin n → ℝ),
      xiLogdefectFiniteZerothMoment center radius mass =
        2 * Real.pi * ∑ i, mass i * radius i) ∧
    (∀ {n : ℕ} (center radius mass : Fin n → ℝ),
      xiLogdefectFiniteFirstMoment center radius mass =
        2 * Real.pi * ∑ i, mass i * radius i * center i) ∧
    (∀ {n : ℕ} (center radius mass : Fin n → ℝ) (a b : ℝ),
      xiLogdefectFiniteAffineMoment center radius mass a b =
        2 * Real.pi * ∑ i, mass i * radius i * (a * center i + b)) := by
  have hKernel :
      ∀ γ δ, 0 < δ → δ ≤ 1 / 2 →
        ∀ x, xiLogdefectAffineKernel γ δ x = xiLogdefectAffinePoissonKernel γ δ x := by
    intro γ δ hδ hδ' x
    have hlower : 0 < xiLogdefectAffineBandLower δ := by
      unfold xiLogdefectAffineBandLower
      linarith
    have hupper : 0 < xiLogdefectAffineBandUpper δ := by
      unfold xiLogdefectAffineBandUpper
      linarith
    simpa [xiLogdefectAffineKernel, xiLogdefectAffinePoissonKernel, xiLogdefectAffineBandLower,
      xiLogdefectAffineBandUpper] using
      xiLogdefectBandpassScalar_eq_primitive_difference x γ (1 - δ) (1 + δ) hlower hupper
  have hZero : ∀ γ δ, xiLogdefectAffineZerothMoment γ δ = 2 * Real.pi * δ := by
    intro γ δ
    unfold xiLogdefectAffineZerothMoment xiLogdefectAffineBandLower xiLogdefectAffineBandUpper
    ring
  have hFirst : ∀ γ δ, xiLogdefectAffineFirstMoment γ δ = 2 * Real.pi * δ * γ := by
    intro γ δ
    unfold xiLogdefectAffineFirstMoment
    rw [hZero]
    ring
  have hAffine :
      ∀ γ δ a b, xiLogdefectAffineMoment γ δ a b = 2 * Real.pi * δ * (a * γ + b) := by
    intro γ δ a b
    unfold xiLogdefectAffineMoment xiLogdefectAffineFirstMoment xiLogdefectAffineZerothMoment
      xiLogdefectAffineBandLower xiLogdefectAffineBandUpper
    ring
  have hFiniteKernel :
      ∀ {n : ℕ} (center radius mass : Fin n → ℝ),
        (∀ i, 0 < radius i) → (∀ i, radius i ≤ 1 / 2) →
        ∀ x, xiLogdefectFinitePotential x center radius mass =
          xiLogdefectFinitePoissonPotential x center radius mass := by
    intro n center radius mass hpos hhalf x
    unfold xiLogdefectFinitePotential xiLogdefectFinitePoissonPotential
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hKernel (center i) (radius i) (hpos i) (hhalf i) x]
  have hFiniteZero :
      ∀ {n : ℕ} (center radius mass : Fin n → ℝ),
        xiLogdefectFiniteZerothMoment center radius mass =
          2 * Real.pi * ∑ i, mass i * radius i := by
    intro n center radius mass
    unfold xiLogdefectFiniteZerothMoment
    calc
      ∑ i, mass i * xiLogdefectAffineZerothMoment (center i) (radius i)
          = ∑ i, mass i * (2 * Real.pi * radius i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hZero (center i) (radius i)]
      _ = 2 * Real.pi * ∑ i, mass i * radius i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have hFiniteFirst :
      ∀ {n : ℕ} (center radius mass : Fin n → ℝ),
        xiLogdefectFiniteFirstMoment center radius mass =
          2 * Real.pi * ∑ i, mass i * radius i * center i := by
    intro n center radius mass
    unfold xiLogdefectFiniteFirstMoment
    calc
      ∑ i, mass i * xiLogdefectAffineFirstMoment (center i) (radius i)
          = ∑ i, mass i * (2 * Real.pi * radius i * center i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hFirst (center i) (radius i)]
      _ = 2 * Real.pi * ∑ i, mass i * radius i * center i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have hFiniteAffine :
      ∀ {n : ℕ} (center radius mass : Fin n → ℝ) (a b : ℝ),
        xiLogdefectFiniteAffineMoment center radius mass a b =
          2 * Real.pi * ∑ i, mass i * radius i * (a * center i + b) := by
    intro n center radius mass a b
    unfold xiLogdefectFiniteAffineMoment
    calc
      ∑ i, mass i * xiLogdefectAffineMoment (center i) (radius i) a b
          = ∑ i, mass i * (2 * Real.pi * radius i * (a * center i + b)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hAffine (center i) (radius i) a b]
      _ = 2 * Real.pi * ∑ i, mass i * radius i * (a * center i + b) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  exact ⟨hKernel, hZero, hFirst, hAffine, hFiniteKernel, hFiniteZero, hFiniteFirst,
    hFiniteAffine⟩

end Omega.Zeta
