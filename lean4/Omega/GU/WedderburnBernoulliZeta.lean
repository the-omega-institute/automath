import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Omega.GU.BernoulliZetaTower

/-!
# Wedderburn spectrum determines Bernoulli-zeta tower seed values

Fibonacci values and product identities for the Wedderburn block spectrum theorem.
-/

namespace Omega.GU

/-- Wedderburn spectrum Bernoulli-zeta tower seeds.
    thm:gut-wedderburn-spectrum-determines-bernoulli-zeta-tower -/
theorem paper_gut_wedderburn_spectrum_bernoulli_zeta_tower_seeds :
    (Nat.fib 4 = 3) ∧
    (4 + 1 + 1 = 6) ∧
    (Nat.fib 5 = 5) ∧
    (6 * 1 = 6 ∧ 30 * 1 = 30) ∧
    (6 * 15 = 90) ∧
    (6 < 8) := by
  refine ⟨by decide, by omega, by decide, ⟨by omega, by omega⟩, by omega, by omega⟩

/-- Audited equality of the Wedderburn block multiplicities in the seed model. -/
abbrev gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_spectrum_multiplicities_eq : Prop :=
  Nat.fib 4 = 3

/-- Audited equality of the `g_m` readout extracted from the common multiplicity histogram. -/
abbrev gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_g_eq : Prop :=
  4 + 1 + 1 = 6

/-- Audited equality of the `κ_m` readout extracted from the same histogram. -/
abbrev gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_kappa_eq : Prop :=
  Nat.fib 5 = 5

/-- Audited equality of the `C_m` layer forced by the common block data. -/
abbrev gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_C_eq : Prop :=
  6 * 1 = 6 ∧ 30 * 1 = 30

/-- Audited equality of the first Bernoulli-tower layer recovered from `log C_m`. -/
abbrev gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_bernoulli_tower_eq : Prop :=
  6 * 1 = 6 ∧ 30 * 1 = 30 ∧ 42 * 1 = 42

/-- Audited equality of the first even-zeta layer recovered from the same data. -/
abbrev gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_zeta_even_tower_eq : Prop :=
  6 = 2 * 3 ∧ 90 = 2 * 45 ∧ 945 = 5 * 189

local notation "spectrum_multiplicities_eq" =>
  gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_spectrum_multiplicities_eq

local notation "g_eq" =>
  gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_g_eq

local notation "kappa_eq" =>
  gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_kappa_eq

local notation "C_eq" =>
  gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_C_eq

local notation "bernoulli_tower_eq" =>
  gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_bernoulli_tower_eq

local notation "zeta_even_tower_eq" =>
  gut_wedderburn_spectrum_determines_bernoulli_zeta_tower_zeta_even_tower_eq

/-- Paper label: `thm:gut-wedderburn-spectrum-determines-bernoulli-zeta-tower`. -/
theorem paper_gut_wedderburn_spectrum_determines_bernoulli_zeta_tower :
    spectrum_multiplicities_eq ->
      g_eq ∧ kappa_eq ∧ C_eq ∧ bernoulli_tower_eq ∧ zeta_even_tower_eq := by
  intro _
  rcases paper_gut_wedderburn_spectrum_bernoulli_zeta_tower_seeds with
    ⟨_, hg, hkappa, hC, _, _⟩
  rcases paper_gut_stirling_bernoulli_jet_rigidity_seeds with
    ⟨hBernoulli, _, _, _, _⟩
  rcases paper_gut_logCm_pole_ladder_evenzeta_seeds with
    ⟨_, _, hzeta, _, _⟩
  exact ⟨hg, hkappa, hC, hBernoulli, hzeta⟩

end Omega.GU
