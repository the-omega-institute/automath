import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9f-local-normalization-step-lower-bound`. -/
theorem paper_xi_time_part9f_local_normalization_step_lower_bound {Ω : Type*}
    (prob : Set Ω → ℝ) (G T : ℕ → Ω → ℝ) (R a c : ℝ) (m : ℕ) (hm : 0 < m)
    (hR : 0 < R) (hstep : ∀ ω, G m ω ≤ R * T m ω)
    (hmono : ∀ A B : Set Ω, A ⊆ B → prob A ≤ prob B)
    (htail : prob {ω | G m ω / (m : ℝ) ≤ a * R} ≤ Real.exp (-c * (m : ℝ))) :
    prob {ω | T m ω / (m : ℝ) ≤ a} ≤ Real.exp (-c * (m : ℝ)) := by
  have hm_real : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsubset :
      {ω | T m ω / (m : ℝ) ≤ a} ⊆ {ω | G m ω / (m : ℝ) ≤ a * R} := by
    intro ω hω
    have hGdiv : G m ω / (m : ℝ) ≤ (R * T m ω) / (m : ℝ) :=
      div_le_div_of_nonneg_right (hstep ω) hm_real.le
    have hTdiv : R * (T m ω / (m : ℝ)) ≤ R * a :=
      mul_le_mul_of_nonneg_left hω hR.le
    calc
      G m ω / (m : ℝ) ≤ (R * T m ω) / (m : ℝ) := hGdiv
      _ = R * (T m ω / (m : ℝ)) := by ring
      _ ≤ R * a := hTdiv
      _ = a * R := by ring
  exact le_trans (hmono _ _ hsubset) htail

end Omega.Zeta
