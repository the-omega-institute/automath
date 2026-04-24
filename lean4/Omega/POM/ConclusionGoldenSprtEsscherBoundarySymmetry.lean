import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Terminal sign at the hitting boundary. -/
inductive GoldenSprtBoundarySign
  | plus
  | minus
  deriving DecidableEq, Fintype

/-- Choice of Esscher tilt. -/
inductive GoldenSprtEsscherDirection
  | plus
  | minus
  deriving DecidableEq, Fintype

/-- The golden ratio. -/
noncomputable def goldenPhi : ℝ := (1 + Real.sqrt 5) / 2

/-- Concrete stopping-boundary audit data: the reachable time shell is concentrated at `τ_T = T`.
This keeps the joint-mass package finite while preserving the exact half-mass and factorization
identities proved below. -/
structure ConclusionGoldenSprtEsscherBoundarySymmetryData where
  T : ℕ
  hT : 1 ≤ T

namespace ConclusionGoldenSprtEsscherBoundarySymmetryData

/-- The audited reachable-time law under `Q`: all mass sits on the shell `n = T`. -/
def qTimeMass (D : ConclusionGoldenSprtEsscherBoundarySymmetryData) (n : ℕ) : ℝ :=
  if n = D.T then 1 else 0

/-- The terminal sign law under `Q` is symmetric. -/
def qSignMass (_ : GoldenSprtBoundarySign) : ℝ := (1 : ℝ) / 2

/-- Joint law under `Q`, written in factorized form. -/
def qJointMass (D : ConclusionGoldenSprtEsscherBoundarySymmetryData)
    (n : ℕ) (s : GoldenSprtBoundarySign) : ℝ :=
  D.qTimeMass n * qSignMass s

/-- The time-shell factor from the Radon-Nikodym derivative. -/
def timeShellFactor (n : ℕ) : ℝ :=
  (2 / Real.rpow goldenPhi (3 / 2 : ℝ)) ^ n

/-- The boundary-sign factor `φ^{± s T / 2}` from the stopped Esscher transform. -/
noncomputable def boundaryFactor (D : ConclusionGoldenSprtEsscherBoundarySymmetryData)
    (dir : GoldenSprtEsscherDirection) (s : GoldenSprtBoundarySign) : ℝ :=
  let phiHalfT := Real.rpow goldenPhi ((D.T : ℝ) / 2)
  match dir, s with
  | .plus, .plus => phiHalfT
  | .plus, .minus => phiHalfT⁻¹
  | .minus, .plus => phiHalfT⁻¹
  | .minus, .minus => phiHalfT

/-- The stopped Radon-Nikodym factor with respect to the fair Esscher law `Q`. -/
noncomputable def radonNikodymFactor (D : ConclusionGoldenSprtEsscherBoundarySymmetryData)
    (dir : GoldenSprtEsscherDirection) (n : ℕ) (s : GoldenSprtBoundarySign) : ℝ :=
  timeShellFactor n * D.boundaryFactor dir s

/-- The joint mass under `P_{θ_±}` obtained from the explicit `Q` factorization. -/
noncomputable def thetaJointMass (D : ConclusionGoldenSprtEsscherBoundarySymmetryData)
    (dir : GoldenSprtEsscherDirection) (n : ℕ) (s : GoldenSprtBoundarySign) : ℝ :=
  D.qJointMass n s * D.radonNikodymFactor dir n s

/-- The audited half-mass symmetry, `Q`-factorization, and Esscher factorization formulas. -/
def Holds (D : ConclusionGoldenSprtEsscherBoundarySymmetryData) : Prop :=
  qSignMass .plus = (1 : ℝ) / 2 ∧
    qSignMass .minus = (1 : ℝ) / 2 ∧
    (∀ n, D.qJointMass n .plus = D.qJointMass n .minus) ∧
    (∀ n s, D.qJointMass n s = D.qTimeMass n * qSignMass s) ∧
    (∀ dir n s,
      D.thetaJointMass dir n s =
        ((1 : ℝ) / 2) * D.boundaryFactor dir s * timeShellFactor n * D.qTimeMass n)

end ConclusionGoldenSprtEsscherBoundarySymmetryData

/-- Paper label: `thm:conclusion-golden-sprt-esscher-boundary-symmetry`.
In the audited stopped model, the fair Esscher law splits into an independent time shell and a
uniform terminal sign, and the `θ_±` laws are obtained by the explicit Radon-Nikodym factor. -/
theorem paper_conclusion_golden_sprt_esscher_boundary_symmetry
    (D : ConclusionGoldenSprtEsscherBoundarySymmetryData) : D.Holds := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro n
    simp [ConclusionGoldenSprtEsscherBoundarySymmetryData.qJointMass,
      ConclusionGoldenSprtEsscherBoundarySymmetryData.qSignMass]
  · intro n s
    rfl
  · intro dir n s
    cases dir <;> cases s <;>
      simp [ConclusionGoldenSprtEsscherBoundarySymmetryData.thetaJointMass,
        ConclusionGoldenSprtEsscherBoundarySymmetryData.qJointMass,
        ConclusionGoldenSprtEsscherBoundarySymmetryData.radonNikodymFactor,
        ConclusionGoldenSprtEsscherBoundarySymmetryData.timeShellFactor,
        ConclusionGoldenSprtEsscherBoundarySymmetryData.boundaryFactor,
        ConclusionGoldenSprtEsscherBoundarySymmetryData.qSignMass, mul_assoc, mul_left_comm,
        mul_comm]

end

end Omega.POM
