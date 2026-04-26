import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open Filter
open scoped BigOperators Topology

/-- Fiber-mean-zero part of an observable relative to the visible projection. -/
def xi_time_part9za_window6_area_pairing_lifted_collapse_fiberMeanZero
    {Ω W : Type*} (F : Ω → ℝ) (π : Ω → W) (Fbar : W → ℝ) : Ω → ℝ :=
  fun ω => F ω - Fbar (π ω)

/-- Finite area pairing used in the window-`6` lifted-collapse corollary. -/
noncomputable def xi_time_part9za_window6_area_pairing_lifted_collapse_pairing
    {α β : Type*} (δ : ℝ) (Λ : Finset α) (φ : α → ℝ) (obs : α → β) (G : β → ℝ) : ℝ :=
  δ ^ 2 * Finset.sum Λ (fun x => φ x * G (obs x))

/-- Paper label: `cor:xi-time-part9za-window6-area-pairing-lifted-collapse`.
Split the lifted observable into its fiber average plus its fiber-mean-zero part; the difference of
the two pairings is exactly the pairing of the mean-zero observable, so any previously verified
strict-locality `L²`-collapse transfers immediately. -/
theorem paper_xi_time_part9za_window6_area_pairing_lifted_collapse
    {α Ω W : Type*}
    (δ : ℕ → ℝ) (Λ : ℕ → Finset α) (φ : α → ℝ)
    (ω : ℕ → α → Ω) (w : ℕ → α → W)
    (F : Ω → ℝ) (π : Ω → W) (Fbar : W → ℝ)
    (hvis : ∀ n x, π (ω n x) = w n x)
    (hstrict :
      Tendsto
        (fun n =>
          xi_time_part9za_window6_area_pairing_lifted_collapse_pairing
            (δ n) (Λ n) φ (ω n)
            (xi_time_part9za_window6_area_pairing_lifted_collapse_fiberMeanZero F π Fbar))
        atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        xi_time_part9za_window6_area_pairing_lifted_collapse_pairing (δ n) (Λ n) φ (ω n) F -
          xi_time_part9za_window6_area_pairing_lifted_collapse_pairing
            (δ n) (Λ n) φ (w n) Fbar)
      atTop (𝓝 0) := by
  have hEq :
      (fun n =>
        xi_time_part9za_window6_area_pairing_lifted_collapse_pairing (δ n) (Λ n) φ (ω n) F -
          xi_time_part9za_window6_area_pairing_lifted_collapse_pairing
            (δ n) (Λ n) φ (w n) Fbar) =
        (fun n =>
          xi_time_part9za_window6_area_pairing_lifted_collapse_pairing
            (δ n) (Λ n) φ (ω n)
            (xi_time_part9za_window6_area_pairing_lifted_collapse_fiberMeanZero F π Fbar)) := by
    funext n
    unfold xi_time_part9za_window6_area_pairing_lifted_collapse_pairing
      xi_time_part9za_window6_area_pairing_lifted_collapse_fiberMeanZero
    calc
      δ n ^ 2 * Finset.sum (Λ n) (fun x => φ x * F (ω n x)) -
          δ n ^ 2 * Finset.sum (Λ n) (fun x => φ x * Fbar (w n x))
          =
            δ n ^ 2 *
              (Finset.sum (Λ n) (fun x => φ x * F (ω n x)) -
                Finset.sum (Λ n) (fun x => φ x * Fbar (w n x))) := by
            ring
      _ = δ n ^ 2 * Finset.sum (Λ n) (fun x => φ x * F (ω n x) - φ x * Fbar (w n x)) := by
            rw [Finset.sum_sub_distrib]
      _ = δ n ^ 2 * Finset.sum (Λ n) (fun x => φ x * (F (ω n x) - Fbar (π (ω n x)))) := by
            congr 1
            apply Finset.sum_congr rfl
            intro x hx
            rw [hvis]
            ring
      _ = xi_time_part9za_window6_area_pairing_lifted_collapse_pairing (δ n) (Λ n) φ (ω n)
            (xi_time_part9za_window6_area_pairing_lifted_collapse_fiberMeanZero F π Fbar) := by
            rfl
  simpa only [hEq] using hstrict

end Omega.Zeta
