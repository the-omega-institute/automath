import Mathlib

namespace Omega.GroupUnification

open scoped Topology

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the tilt-dynamics corollary in
    `submitted_2026_zero_jitter_information_clocks_parry_gibbs_rigidity_jtp`.
    cor:tilt-dynamics -/
theorem paper_zero_jitter_tilt_dynamics
    (T : ℝ → ℝ → ℝ) (L : ℝ → ℝ) (phiInv : ℝ)
    (hCoord : ∀ t p, L (T t p) = (1 - t) * L p)
    (hZero : ∀ p, L p = 0 ↔ p = phiInv)
    (hInj : Function.Injective L) :
    (∀ t n p, L ((T t)^[n] p) = (1 - t) ^ n * L p) ∧
      (∀ t, T t phiInv = phiInv) ∧
      (∀ t n p, (T t)^[n] p = T (1 - (1 - t) ^ n) p) ∧
      (∀ t p, t ≠ 0 → T t p = p → p = phiInv) ∧
      (∀ t p, 0 < t → t < 2 →
        Filter.Tendsto (fun n : ℕ => L ((T t)^[n] p)) Filter.atTop (𝓝 0)) := by
  have hIterCoord : ∀ t n p, L ((T t)^[n] p) = (1 - t) ^ n * L p := by
    intro t n
    induction n with
    | zero =>
        intro p
        simp
    | succ n ih =>
        intro p
        rw [Function.iterate_succ_apply']
        calc
          L (T t ((T t)^[n] p)) = (1 - t) * L ((T t)^[n] p) := hCoord t ((T t)^[n] p)
          _ = (1 - t) * ((1 - t) ^ n * L p) := by rw [ih]
          _ = (1 - t) ^ (n + 1) * L p := by ring
  have hFixed : ∀ t, T t phiInv = phiInv := by
    intro t
    apply (hZero _).mp
    calc
      L (T t phiInv) = (1 - t) * L phiInv := hCoord t phiInv
      _ = (1 - t) * 0 := by rw [(hZero _).mpr rfl]
      _ = 0 := by ring
  have hIterate : ∀ t n p, (T t)^[n] p = T (1 - (1 - t) ^ n) p := by
    intro t n p
    apply hInj
    rw [hIterCoord]
    calc
      (1 - t) ^ n * L p = (1 - (1 - (1 - t) ^ n)) * L p := by ring
      _ = L (T (1 - (1 - t) ^ n) p) := by rw [hCoord]
  have hUnique : ∀ t p, t ≠ 0 → T t p = p → p = phiInv := by
    intro t p ht hFix
    apply (hZero _).mp
    have hLp : L p = (1 - t) * L p := by simpa [hFix] using hCoord t p
    have hMul : t * L p = 0 := by nlinarith [hLp]
    exact (mul_eq_zero.mp hMul).resolve_left ht
  have hAttract : ∀ t p, 0 < t → t < 2 →
      Filter.Tendsto (fun n : ℕ => L ((T t)^[n] p)) Filter.atTop (𝓝 0) := by
    intro t p ht0 ht2
    have habs : |1 - t| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have hPow : Filter.Tendsto (fun n : ℕ => (1 - t) ^ n) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs
    have hMul :
        Filter.Tendsto (fun n : ℕ => (1 - t) ^ n * L p) Filter.atTop (𝓝 (0 * L p)) :=
      hPow.mul_const (L p)
    simpa [hIterCoord, zero_mul] using hMul
  exact ⟨hIterCoord, hFixed, hIterate, hUnique, hAttract⟩

end Omega.GroupUnification
