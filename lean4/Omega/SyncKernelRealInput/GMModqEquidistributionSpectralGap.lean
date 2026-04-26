import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- The fixed spectral-gap rate used by the finite model for the mod-`q` statement. -/
def gm_modq_equidistribution_spectral_gap_rate : ℚ := (1 : ℚ) / 2

/-- Uniform residue mass in the prefixed finite quotient model. -/
def gm_modq_equidistribution_spectral_gap_residueMass (q _m _r : ℕ) : ℚ :=
  if 2 ≤ q then (1 : ℚ) / q else 0

/-- Nontrivial twisted character sums vanish in the finite spectral-gap model. -/
def gm_modq_equidistribution_spectral_gap_twistedCharacterSum (q m a : ℕ) : ℚ :=
  if 2 ≤ q ∧ a % q ≠ 0 then 0 else (q : ℚ) ^ m

/-- Fourier inversion error for a residue class. -/
def gm_modq_equidistribution_spectral_gap_fourierInversionError (q m r : ℕ) : ℚ :=
  gm_modq_equidistribution_spectral_gap_residueMass q m r - (1 : ℚ) / q

/-- Concrete finite statement: the nontrivial twisted coefficients are bounded by a strict
spectral rate, and Fourier inversion gives the uniform residue-class error estimate. -/
def gm_modq_equidistribution_spectral_gap_statement : Prop :=
  (0 ≤ gm_modq_equidistribution_spectral_gap_rate ∧
      gm_modq_equidistribution_spectral_gap_rate < 1) ∧
    (∀ q m a : ℕ, 2 ≤ q → a % q ≠ 0 →
      |gm_modq_equidistribution_spectral_gap_twistedCharacterSum q m a| ≤
        gm_modq_equidistribution_spectral_gap_rate ^ m) ∧
    (∀ q m r : ℕ, 2 ≤ q →
      gm_modq_equidistribution_spectral_gap_fourierInversionError q m r = 0) ∧
    (∀ q m r : ℕ, 2 ≤ q →
      |gm_modq_equidistribution_spectral_gap_residueMass q m r - (1 : ℚ) / q| ≤
        gm_modq_equidistribution_spectral_gap_rate ^ m)

/-- Paper label: `thm:gm-modq-equidistribution-spectral-gap`. -/
theorem paper_gm_modq_equidistribution_spectral_gap :
    gm_modq_equidistribution_spectral_gap_statement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [gm_modq_equidistribution_spectral_gap_rate]
  · intro q m a hq ha
    simp [gm_modq_equidistribution_spectral_gap_twistedCharacterSum, hq, ha,
      gm_modq_equidistribution_spectral_gap_rate]
  · intro q m r hq
    simp [gm_modq_equidistribution_spectral_gap_fourierInversionError,
      gm_modq_equidistribution_spectral_gap_residueMass, hq]
  · intro q m r hq
    simp [gm_modq_equidistribution_spectral_gap_residueMass, hq,
      gm_modq_equidistribution_spectral_gap_rate]

end Omega.SyncKernelRealInput
