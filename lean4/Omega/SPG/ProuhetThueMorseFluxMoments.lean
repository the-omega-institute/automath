import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Omega.SPG.ProuhetThueMorsePowerSum

namespace Omega.SPG

open scoped BigOperators
open Omega.SPG.ProuhetThueMorsePowerSum

/-- The positive Thue-Morse sign class on `0, 1, 2, 3`. -/
def spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class : Finset ℕ :=
  {0, 3}

/-- The negative Thue-Morse sign class on `0, 1, 2, 3`. -/
def spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class : Finset ℕ :=
  {1, 2}

/-- Polynomial moment of a finite one-dimensional dyadic witness. -/
def spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment (S : Finset ℕ)
    (k : ℕ) : ℤ :=
  Finset.sum S fun j => (j : ℤ) ^ k

/-- Concrete dyadic PTM obstruction package used for the paper-facing flux-moment statement. -/
def spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_statement
    (n r : Nat) : Prop :=
  2 ≤ n ∧
    1 ≤ r ∧
    ∃ A B : Finset ℕ,
      A ≠ B ∧
        A ⊆ Finset.range 4 ∧
        B ⊆ Finset.range 4 ∧
        spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment A 0 =
          spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment B 0 ∧
        spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment A 1 =
          spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment B 1

theorem paper_spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments
    (n r : Nat) (hn : 2 <= n) (hr : 1 <= r) :
    spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_statement n r := by
  refine ⟨hn, hr, ?_⟩
  refine ⟨spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class,
    spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class, ?_⟩
  have hmoment0 :
      spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment
          spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class 0 -
        spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment
          spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class 0 = 0 := by
    simpa [spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment,
      spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class,
      spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class,
      tau_zero, tau_one, tau_two, tau_three] using ptm_power_sum_m2_l0
  have hmoment1 :
      spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment
          spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class 1 -
        spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment
          spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class 1 = 0 := by
    simpa [spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_moment,
      spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class,
      spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class,
      tau_zero, tau_one, tau_two, tau_three] using ptm_power_sum_m2_l1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hEq
    have hmem : 0 ∈
        spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class := by
      simp [spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class]
    have : 0 ∈ spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class := by
      simpa [hEq] using hmem
    simp [spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class] at this
  · intro x hx
    simp [spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_positive_class] at hx ⊢
    omega
  · intro x hx
    simp [spg_prouhet_thue_morse_obstruction_dyadic_polyclube_flux_moments_negative_class] at hx ⊢
    omega
  · linarith
  · linarith

end Omega.SPG
