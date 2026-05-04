import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Filter Topology

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-bounded-fourier-window-cannot-exhaust-collision-energy`. -/
theorem paper_conclusion_bounded_fourier_window_cannot_exhaust_collision_energy
    (M : ℕ → ℕ)
    (a : (m : ℕ) → Fin (M m) → ℝ)
    (A : (m : ℕ) → Finset (Fin (M m)))
    (energy : ℕ → ℝ)
    (C : ℕ)
    (henergy : Filter.Tendsto energy Filter.atTop Filter.atTop)
    (hbound : ∀ m k, 0 ≤ a m k ∧ a m k ≤ 1)
    (henergy_eq : ∀ m, energy m = ∑ k : Fin (M m), (a m k)^2)
    (hA : ∀ m, (A m).card ≤ C) :
    Filter.Tendsto (fun m : ℕ => (∑ k ∈ (A m)ᶜ, (a m k)^2)) Filter.atTop Filter.atTop := by
  have henergy_minus :
      Tendsto (fun m : ℕ => energy m - (C : ℝ)) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-(C : ℝ)) henergy)
  refine tendsto_atTop_mono ?_ henergy_minus
  intro m
  let f : Fin (M m) → ℝ := fun k => (a m k)^2
  have hselected_le : (∑ k ∈ A m, f k) ≤ (C : ℝ) := by
    calc
      (∑ k ∈ A m, f k) ≤ ∑ k ∈ A m, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro k _hk
        have hkbound := hbound m k
        dsimp [f]
        nlinarith
      _ = ((A m).card : ℝ) := by simp
      _ ≤ (C : ℝ) := by exact_mod_cast hA m
  have hsplit :
      energy m = (∑ k ∈ A m, f k) + ∑ k ∈ (A m)ᶜ, f k := by
    rw [henergy_eq m]
    have hsum_split :
        (∑ k ∈ A m, f k) + ∑ k ∈ (A m)ᶜ, f k = ∑ k : Fin (M m), f k := by
      simp [Finset.compl_eq_univ_sdiff, f]
    exact hsum_split.symm
  calc
    energy m - (C : ℝ)
        = (∑ k ∈ A m, f k) + ∑ k ∈ (A m)ᶜ, f k - (C : ℝ) := by rw [hsplit]
    _ ≤ ∑ k ∈ (A m)ᶜ, f k := by linarith

end Omega.Conclusion
