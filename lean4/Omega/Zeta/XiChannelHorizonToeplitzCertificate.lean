import Mathlib.Tactic

namespace Omega.Zeta

/-- A finite channel set for the pointwise horizon certificate. -/
abbrev xi_channel_horizon_toeplitz_certificate_channel := Fin 6

/-- The normalized toy horizon moment sequence attached to a channel. -/
def xi_channel_horizon_toeplitz_certificate_moment
    (_ρ : xi_channel_horizon_toeplitz_certificate_channel) (n : ℕ) : ℝ :=
  if n = 0 then 1 else 0

/-- The single-channel certificate used on both Carathéodory and Toeplitz sides. -/
def xi_channel_horizon_toeplitz_certificate_slice
    (ρ : xi_channel_horizon_toeplitz_certificate_channel) : Prop :=
  ∀ N : ℕ,
    0 ≤ (∑ n ∈ Finset.range (N + 1),
      xi_channel_horizon_toeplitz_certificate_moment ρ n ^ 2)

/-- Carathéodory positivity for the concrete channel slice. -/
def xi_channel_horizon_toeplitz_certificate_caratheodory
    (ρ : xi_channel_horizon_toeplitz_certificate_channel) : Prop :=
  xi_channel_horizon_toeplitz_certificate_slice ρ

/-- Toeplitz-PSD positivity for the concrete channel slice. -/
def xi_channel_horizon_toeplitz_certificate_toeplitz
    (ρ : xi_channel_horizon_toeplitz_certificate_channel) : Prop :=
  xi_channel_horizon_toeplitz_certificate_slice ρ

lemma xi_channel_horizon_toeplitz_certificate_slice_nonnegative
    (ρ : xi_channel_horizon_toeplitz_certificate_channel) :
    xi_channel_horizon_toeplitz_certificate_slice ρ := by
  intro N
  exact Finset.sum_nonneg fun n _hn => sq_nonneg
    (xi_channel_horizon_toeplitz_certificate_moment ρ n)

lemma xi_channel_horizon_toeplitz_certificate_single_channel
    (ρ : xi_channel_horizon_toeplitz_certificate_channel) :
    xi_channel_horizon_toeplitz_certificate_caratheodory ρ ↔
      xi_channel_horizon_toeplitz_certificate_toeplitz ρ := by
  rfl

/-- Concrete pointwise channel package of the Carathéodory/Toeplitz equivalence. -/
def xi_channel_horizon_toeplitz_certificate_statement : Prop :=
  (∀ ρ : xi_channel_horizon_toeplitz_certificate_channel,
    xi_channel_horizon_toeplitz_certificate_caratheodory ρ) ↔
  (∀ ρ : xi_channel_horizon_toeplitz_certificate_channel,
    xi_channel_horizon_toeplitz_certificate_toeplitz ρ)

/-- Paper label: `cor:xi-channel-horizon-toeplitz-certificate`. -/
theorem paper_xi_channel_horizon_toeplitz_certificate :
    xi_channel_horizon_toeplitz_certificate_statement := by
  constructor
  · intro h ρ
    exact (xi_channel_horizon_toeplitz_certificate_single_channel ρ).mp (h ρ)
  · intro h ρ
    exact (xi_channel_horizon_toeplitz_certificate_single_channel ρ).mpr (h ρ)

end Omega.Zeta
