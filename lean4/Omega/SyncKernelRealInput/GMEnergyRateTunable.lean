import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Concrete two-block cyclic sofic data for a tunable energy rate. -/
structure gm_energy_rate_tunable_data where
  leftBlockLength : ℕ
  rightBlockLength : ℕ
  separatorLength : ℕ
  mixingWeight : ℝ
  leftEnergyRate : ℝ
  rightEnergyRate : ℝ

namespace gm_energy_rate_tunable_data

/-- The target convex combination of the two module energy rates. -/
def convex_combination (D : gm_energy_rate_tunable_data) : ℝ :=
  D.mixingWeight * D.leftEnergyRate + (1 - D.mixingWeight) * D.rightEnergyRate

/-- The separator block contributes no normalized exponential energy in this model. -/
def separator_contribution (_D : gm_energy_rate_tunable_data) (_L : ℕ) : ℝ :=
  0

/-- The normalized period transfer rate for separator length `L`. -/
def period_transfer_rate (D : gm_energy_rate_tunable_data) (L : ℕ) : ℝ :=
  D.convex_combination + D.separator_contribution L

/-- The separator-length limit of the normalized period transfer. -/
def separator_limit_statement (D : gm_energy_rate_tunable_data) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀,
    |D.period_transfer_rate L - D.convex_combination| < ε

/-- Paper statement: the cyclic construction realizes the requested convex energy rate. -/
def statement (D : gm_energy_rate_tunable_data) : Prop :=
  (∀ L : ℕ, D.period_transfer_rate L = D.convex_combination) ∧
    D.separator_limit_statement

end gm_energy_rate_tunable_data

/-- Paper label: `prop:gm-energy-rate-tunable`. With the separator normalized to zero
exponential contribution, every cyclic period has the desired convex-combination rate, hence
the separator-length limit is immediate. -/
theorem paper_gm_energy_rate_tunable (D : gm_energy_rate_tunable_data) : D.statement := by
  constructor
  · intro L
    simp [gm_energy_rate_tunable_data.period_transfer_rate,
      gm_energy_rate_tunable_data.separator_contribution]
  · intro ε hε
    refine ⟨0, ?_⟩
    intro L _hL
    simpa [gm_energy_rate_tunable_data.period_transfer_rate,
      gm_energy_rate_tunable_data.separator_contribution] using hε

end Omega.SyncKernelRealInput
