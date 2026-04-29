import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-jensen-modulus-recursive-observability-stability`. -/
theorem paper_xi_jensen_modulus_recursive_observability_stability
    (P Ptilde a : Nat → ℝ) (eps : ℝ) (_hP0 : P 0 = 1)
    (hrec : forall k, 1 <= k -> P k = P (k - 1) * a k)
    (hpos : forall k, 0 < P k) (htilde_pos : forall k, 0 < Ptilde k)
    (hstability : forall k,
      Real.exp (-eps) * P k <= Ptilde k ∧ Ptilde k <= Real.exp eps * P k) :
    (forall k, 1 <= k -> a k = P k / P (k - 1)) ∧
      (forall k, 1 <= k ->
        Real.exp (-2 * eps) * a k <= Ptilde k / Ptilde (k - 1) ∧
          Ptilde k / Ptilde (k - 1) <= Real.exp (2 * eps) * a k) := by
  constructor
  · intro k hk
    have hprev_ne : P (k - 1) ≠ 0 := ne_of_gt (hpos (k - 1))
    have hkrec : P k = P (k - 1) * a k := hrec k hk
    calc
      a k = (P (k - 1) * a k) / P (k - 1) := by
        field_simp [hprev_ne]
      _ = P k / P (k - 1) := by rw [← hkrec]
  · intro k hk
    have hprev_pos : 0 < P (k - 1) := hpos (k - 1)
    have hprev_tilde_pos : 0 < Ptilde (k - 1) := htilde_pos (k - 1)
    have hratio : a k = P k / P (k - 1) := by
      have hprev_ne : P (k - 1) ≠ 0 := ne_of_gt hprev_pos
      have hkrec : P k = P (k - 1) * a k := hrec k hk
      calc
        a k = (P (k - 1) * a k) / P (k - 1) := by
          field_simp [hprev_ne]
        _ = P k / P (k - 1) := by rw [← hkrec]
    have ha_pos : 0 < a k := by
      rw [hratio]
      exact div_pos (hpos k) hprev_pos
    have hlow_k : Real.exp (-eps) * P k <= Ptilde k := (hstability k).1
    have hup_k : Ptilde k <= Real.exp eps * P k := (hstability k).2
    have hlow_prev : Real.exp (-eps) * P (k - 1) <= Ptilde (k - 1) :=
      (hstability (k - 1)).1
    have hup_prev : Ptilde (k - 1) <= Real.exp eps * P (k - 1) :=
      (hstability (k - 1)).2
    have hexp_neg2_pos : 0 < Real.exp (-2 * eps) := Real.exp_pos _
    have hexp_pos2_pos : 0 < Real.exp (2 * eps) := Real.exp_pos _
    constructor
    · rw [le_div_iff₀ hprev_tilde_pos]
      calc
        Real.exp (-2 * eps) * a k * Ptilde (k - 1)
            <= Real.exp (-2 * eps) * a k * (Real.exp eps * P (k - 1)) := by
          exact mul_le_mul_of_nonneg_left hup_prev (mul_nonneg hexp_neg2_pos.le ha_pos.le)
        _ = Real.exp (-eps) * P k := by
          rw [hratio]
          field_simp [ne_of_gt hprev_pos]
          calc
            Real.exp (-(2 * eps)) * P k * Real.exp eps =
                P k * (Real.exp (-(2 * eps)) * Real.exp eps) := by ring
            _ = P k * Real.exp (-(2 * eps) + eps) := by rw [Real.exp_add]
            _ = P k * Real.exp (-eps) := by ring_nf
        _ <= Ptilde k := hlow_k
    · rw [div_le_iff₀ hprev_tilde_pos]
      calc
        Ptilde k <= Real.exp eps * P k := hup_k
        _ = Real.exp (2 * eps) * a k * (Real.exp (-eps) * P (k - 1)) := by
          rw [hratio]
          field_simp [ne_of_gt hprev_pos]
          calc
            Real.exp eps * P k = P k * Real.exp eps := by ring
            _ = P k * Real.exp (2 * eps + -eps) := by ring_nf
            _ = P k * (Real.exp (2 * eps) * Real.exp (-eps)) := by
              rw [Real.exp_add]
            _ = P k * Real.exp (2 * eps) * Real.exp (-eps) := by ring
        _ <= Real.exp (2 * eps) * a k * Ptilde (k - 1) := by
          exact mul_le_mul_of_nonneg_left hlow_prev (mul_nonneg hexp_pos2_pos.le ha_pos.le)

end Omega.Zeta
