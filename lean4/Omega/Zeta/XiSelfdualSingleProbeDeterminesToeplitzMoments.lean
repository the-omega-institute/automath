import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The endpoint probe value `a₀ = E[((1 - X) / 2)^0]`. -/
def xiSingleProbe0 (m0 : ℝ) : ℝ :=
  m0

/-- The endpoint probe value `a₁ = E[(1 - X) / 2]`. -/
noncomputable def xiSingleProbe1 (m0 m1 : ℝ) : ℝ :=
  (m0 - m1) / 2

/-- The endpoint probe value `a₂ = E[((1 - X) / 2)^2]`. -/
noncomputable def xiSingleProbe2 (m0 m1 m2 : ℝ) : ℝ :=
  (m0 - 2 * m1 + m2) / 4

/-- Binomial inversion for the zeroth real moment. -/
def xiRecoveredMoment0 (a0 : ℝ) : ℝ :=
  a0

/-- Binomial inversion for the first real moment. -/
def xiRecoveredMoment1 (a0 a1 : ℝ) : ℝ :=
  a0 - 2 * a1

/-- Binomial inversion for the second real moment. -/
def xiRecoveredMoment2 (a0 a1 a2 : ℝ) : ℝ :=
  a0 - 4 * a1 + 4 * a2

/-- In the self-dual setting, the first three Toeplitz moments are the first three real Chebyshev
moments of `X = Re ξ`. -/
def xiToeplitzMomentVector (m0 m1 m2 : ℝ) : Fin 3 → ℝ :=
  ![m0, m1, 2 * m2 - m0]

/-- The same Toeplitz moments written in terms of the recovered real moments. -/
def xiRecoveredToeplitzMomentVector (a0 a1 a2 : ℝ) : Fin 3 → ℝ :=
  ![xiRecoveredMoment0 a0, xiRecoveredMoment1 a0 a1,
    2 * xiRecoveredMoment2 a0 a1 a2 - xiRecoveredMoment0 a0]

/-- The first three endpoint probe values determine the first three real moments by binomial
inversion, and therefore determine the corresponding Toeplitz moments in the self-dual setting.
This is the finite-truncation seed of the single-probe reconstruction statement.
    thm:xi-selfdual-single-probe-determines-toeplitz-moments -/
theorem paper_xi_selfdual_single_probe_determines_toeplitz_moments (m0 m1 m2 : ℝ) :
    let a0 := xiSingleProbe0 m0
    let a1 := xiSingleProbe1 m0 m1
    let a2 := xiSingleProbe2 m0 m1 m2
    xiRecoveredMoment0 a0 = m0 ∧
      xiRecoveredMoment1 a0 a1 = m1 ∧
      xiRecoveredMoment2 a0 a1 a2 = m2 ∧
      xiRecoveredToeplitzMomentVector a0 a1 a2 = xiToeplitzMomentVector m0 m1 m2 := by
  dsimp [xiSingleProbe0, xiSingleProbe1, xiSingleProbe2, xiRecoveredMoment0, xiRecoveredMoment1,
    xiRecoveredMoment2, xiRecoveredToeplitzMomentVector, xiToeplitzMomentVector]
  constructor
  · ring_nf
  constructor
  · ring_nf
  constructor
  · ring_nf
  · ext i
    fin_cases i <;> ring_nf

end Omega.Zeta
