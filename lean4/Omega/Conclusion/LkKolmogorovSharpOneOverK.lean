import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The floor expression coming from the discrete Weyl counting law. -/
noncomputable def lkDiscreteCount (k : Nat) (θ : ℝ) : Int :=
  Int.floor ((((2 * k + 1 : Nat) : ℝ) / (2 * Real.pi)) * θ + 1 / 2)

/-- Uniform `1/k` Kolmogorov control against the limiting arc-cosine law, written in the
equivalent angle variable `θ ∈ [0, π]`. -/
def LkKolmogorovSharpOneOverK (k : Nat) : Prop :=
  ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
    |(lkDiscreteCount k θ : ℝ) / k - θ / Real.pi| ≤ 1 / k

/-- `thm:conclusion-Lk-kolmogorov-sharp-1overk` -/
theorem paper_conclusion_lk_kolmogorov_sharp_1overk (k : Nat) (hk : 0 < k) :
    LkKolmogorovSharpOneOverK k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkR_ne : (k : ℝ) ≠ 0 := by positivity
  intro θ hθ0 hθpi
  set A : ℝ := (((2 * k + 1 : Nat) : ℝ) / (2 * Real.pi)) * θ with hA
  set m : Int := Int.floor (A + 1 / 2) with hm
  have hcount : lkDiscreteCount k θ = m := by
    simp [lkDiscreteCount, hA, hm]
  have hm_upper : (m : ℝ) - A ≤ 1 / 2 := by
    have hfloor : (m : ℝ) ≤ A + 1 / 2 := by
      rw [hm]
      exact_mod_cast Int.floor_le (A + 1 / 2)
    linarith
  have hm_lower : -(1 / 2 : ℝ) ≤ (m : ℝ) - A := by
    have hfloor : A + 1 / 2 < (m : ℝ) + 1 := by
      rw [hm]
      exact_mod_cast Int.lt_floor_add_one (A + 1 / 2)
    linarith
  have hm_abs : |(m : ℝ) - A| ≤ 1 / 2 := by
    exact abs_le.mpr ⟨hm_lower, hm_upper⟩
  have hterm1 : |((m : ℝ) - A) / k| ≤ 1 / (2 * k : ℝ) := by
    rw [abs_div, abs_of_pos hkR]
    have hdiv : |(m : ℝ) - A| / k ≤ (1 / 2 : ℝ) / k :=
      div_le_div_of_nonneg_right hm_abs (le_of_lt hkR)
    have hrewrite : (1 / 2 : ℝ) / k = 1 / (2 * k : ℝ) := by
      ring_nf
    calc
      |(m : ℝ) - A| / k ≤ (1 / 2 : ℝ) / k := hdiv
      _ = 1 / (2 * k : ℝ) := hrewrite
  have hcoef :
      ((((2 * k + 1 : Nat) : ℝ) / (2 * Real.pi)) / k - 1 / Real.pi) =
        1 / (2 * Real.pi * k) := by
    field_simp [hkR_ne, Real.pi_ne_zero]
    norm_num
  have hterm2_eq : A / k - θ / Real.pi = θ / (2 * Real.pi * k) := by
    rw [hA]
    calc
      ((((2 * k + 1 : Nat) : ℝ) / (2 * Real.pi)) * θ) / k - θ / Real.pi
          = θ * ((((2 * k + 1 : Nat) : ℝ) / (2 * Real.pi)) / k) - θ * (1 / Real.pi) := by
              ring
      _ = θ * (((((2 * k + 1 : Nat) : ℝ) / (2 * Real.pi)) / k) - 1 / Real.pi) := by ring
      _ = θ * (1 / (2 * Real.pi * k)) := by rw [hcoef]
      _ = θ / (2 * Real.pi * k) := by ring
  have hterm2 : |A / k - θ / Real.pi| ≤ 1 / (2 * k : ℝ) := by
    rw [hterm2_eq]
    have hdenom_nonneg : 0 ≤ 2 * Real.pi * k := by positivity
    have hbound :
        θ / (2 * Real.pi * k) ≤ Real.pi / (2 * Real.pi * k) :=
      div_le_div_of_nonneg_right hθpi hdenom_nonneg
    have hnonneg : 0 ≤ θ / (2 * Real.pi * k) := by positivity
    rw [abs_of_nonneg hnonneg]
    calc
      θ / (2 * Real.pi * k) ≤ Real.pi / (2 * Real.pi * k) := hbound
      _ = 1 / (2 * k : ℝ) := by
        field_simp [hkR_ne, Real.pi_ne_zero]
  have hsplit :
      (m : ℝ) / k - θ / Real.pi = (((m : ℝ) - A) / k) + (A / k - θ / Real.pi) := by
    ring
  calc
    |(lkDiscreteCount k θ : ℝ) / k - θ / Real.pi|
        = |(m : ℝ) / k - θ / Real.pi| := by rw [hcount]
    _ = |(((m : ℝ) - A) / k) + (A / k - θ / Real.pi)| := by rw [hsplit]
    _ ≤ |((m : ℝ) - A) / k| + |A / k - θ / Real.pi| := abs_add_le _ _
    _ ≤ 1 / (2 * k : ℝ) + 1 / (2 * k : ℝ) := add_le_add hterm1 hterm2
    _ = 1 / k := by
      field_simp [hkR_ne]
      ring_nf

end Omega.Conclusion
