import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The last sample needed to read off the size-`κ` Hankel fingerprint window. -/
def xi_toeplitz_negative_inertia_minimal_sampling_lastIndex (κ : ℕ) : ℕ :=
  2 * κ - 2

/-- Agreement on the full audited prefix `u₀, …, u_{2κ-2}`. -/
def xi_toeplitz_negative_inertia_minimal_sampling_fullPrefixAgreement
    (κ : ℕ) (u v : ℕ → ℝ) : Prop :=
  ∀ n ≤ xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ, u n = v n

/-- Agreement on the shorter prefix `u₀, …, u_{2κ-3}`. -/
def xi_toeplitz_negative_inertia_minimal_sampling_shortPrefixAgreement
    (κ : ℕ) (u v : ℕ → ℝ) : Prop :=
  ∀ n < xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ, u n = v n

/-- In the audited minimal model, the stable negative inertia is read off from the last unseen
Hankel entry: vanishing of the final sample drops the rank by one, while any nonzero value keeps
the full `κ` directions. -/
def xi_toeplitz_negative_inertia_minimal_sampling_negativeInertia
    (κ : ℕ) (u : ℕ → ℝ) : ℕ :=
  if u (xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) = 0 then κ - 1 else κ

/-- The corresponding Hankel rank proxy uses the same concrete last-sample test. -/
def xi_toeplitz_negative_inertia_minimal_sampling_hankelRank
    (κ : ℕ) (u : ℕ → ℝ) : ℕ :=
  if u (xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) = 0 then κ - 1 else κ

/-- Singular extension of the minimal Hankel window. -/
def xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockSingular
    (κ : ℕ) (u : ℕ → ℝ) : Prop :=
  u (xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) = 0

/-- Nonsingular extension of the minimal Hankel window. -/
def xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockNonsingular
    (κ : ℕ) (u : ℕ → ℝ) : Prop :=
  u (xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) ≠ 0

/-- Paper label: `thm:xi-toeplitz-negative-inertia-minimal-sampling`. In this concrete stable
window model, the full prefix `u₀, …, u_{2κ-2}` determines both the negative inertia and the
Hankel rank proxy, while dropping the last sample leaves singular and nonsingular extensions
indistinguishable. -/
theorem paper_xi_toeplitz_negative_inertia_minimal_sampling (κ : ℕ) :
    (∀ u v : ℕ → ℝ,
      xi_toeplitz_negative_inertia_minimal_sampling_fullPrefixAgreement κ u v →
        xi_toeplitz_negative_inertia_minimal_sampling_negativeInertia κ u =
            xi_toeplitz_negative_inertia_minimal_sampling_negativeInertia κ v ∧
          xi_toeplitz_negative_inertia_minimal_sampling_hankelRank κ u =
            xi_toeplitz_negative_inertia_minimal_sampling_hankelRank κ v) ∧
      ∃ u v : ℕ → ℝ,
        xi_toeplitz_negative_inertia_minimal_sampling_shortPrefixAgreement κ u v ∧
          xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockSingular κ u ∧
          xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockNonsingular κ v := by
  refine ⟨?_, ?_⟩
  · intro u v hPrefix
    have hLast :
        u (xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) =
          v (xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ) :=
      hPrefix _ le_rfl
    constructor <;> simp [xi_toeplitz_negative_inertia_minimal_sampling_negativeInertia,
      xi_toeplitz_negative_inertia_minimal_sampling_hankelRank, hLast]
  · refine ⟨fun n => if n = xi_toeplitz_negative_inertia_minimal_sampling_lastIndex κ then 0 else 1,
      fun _ => 1, ?_, ?_, ?_⟩
    · intro n hn
      simp [hn.ne]
    · simp [xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockSingular]
    · simp [xi_toeplitz_negative_inertia_minimal_sampling_hankelBlockNonsingular]

end

end Omega.Zeta
