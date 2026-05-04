import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:conclusion-leyang-time-identifiability-three-sampling`. -/
theorem paper_conclusion_leyang_time_identifiability_three_sampling {K : Type*} [Field K]
    (y1 y2 y3 rhs1 rhs2 rhs3 a b c a' b' c' : K) (hy12 : y1 ≠ y2) (hy13 : y1 ≠ y3)
    (hy23 : y2 ≠ y3) (h1 : a * y1 ^ 2 + b * y1 + c = rhs1)
    (h2 : a * y2 ^ 2 + b * y2 + c = rhs2)
    (h3 : a * y3 ^ 2 + b * y3 + c = rhs3)
    (h1' : a' * y1 ^ 2 + b' * y1 + c' = rhs1)
    (h2' : a' * y2 ^ 2 + b' * y2 + c' = rhs2)
    (h3' : a' * y3 ^ 2 + b' * y3 + c' = rhs3) :
    a = a' ∧ b = b' ∧ c = c' := by
  have hz1 : (a - a') * y1 ^ 2 + (b - b') * y1 + (c - c') = 0 := by
    calc
      (a - a') * y1 ^ 2 + (b - b') * y1 + (c - c') =
          (a * y1 ^ 2 + b * y1 + c) - (a' * y1 ^ 2 + b' * y1 + c') := by
        ring
      _ = rhs1 - rhs1 := by rw [h1, h1']
      _ = 0 := by simp
  have hz2 : (a - a') * y2 ^ 2 + (b - b') * y2 + (c - c') = 0 := by
    calc
      (a - a') * y2 ^ 2 + (b - b') * y2 + (c - c') =
          (a * y2 ^ 2 + b * y2 + c) - (a' * y2 ^ 2 + b' * y2 + c') := by
        ring
      _ = rhs2 - rhs2 := by rw [h2, h2']
      _ = 0 := by simp
  have hz3 : (a - a') * y3 ^ 2 + (b - b') * y3 + (c - c') = 0 := by
    calc
      (a - a') * y3 ^ 2 + (b - b') * y3 + (c - c') =
          (a * y3 ^ 2 + b * y3 + c) - (a' * y3 ^ 2 + b' * y3 + c') := by
        ring
      _ = rhs3 - rhs3 := by rw [h3, h3']
      _ = 0 := by simp
  have h12 : (a - a') * (y1 + y2) + (b - b') = 0 := by
    have hdiff :
        ((a - a') * y1 ^ 2 + (b - b') * y1 + (c - c')) -
            ((a - a') * y2 ^ 2 + (b - b') * y2 + (c - c')) = 0 := by
      rw [hz1, hz2]
      simp
    have hfactor :
        (y1 - y2) * ((a - a') * (y1 + y2) + (b - b')) = 0 := by
      calc
        (y1 - y2) * ((a - a') * (y1 + y2) + (b - b')) =
            ((a - a') * y1 ^ 2 + (b - b') * y1 + (c - c')) -
              ((a - a') * y2 ^ 2 + (b - b') * y2 + (c - c')) := by
          ring
        _ = 0 := hdiff
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hy12)
  have h13 : (a - a') * (y1 + y3) + (b - b') = 0 := by
    have hdiff :
        ((a - a') * y1 ^ 2 + (b - b') * y1 + (c - c')) -
            ((a - a') * y3 ^ 2 + (b - b') * y3 + (c - c')) = 0 := by
      rw [hz1, hz3]
      simp
    have hfactor :
        (y1 - y3) * ((a - a') * (y1 + y3) + (b - b')) = 0 := by
      calc
        (y1 - y3) * ((a - a') * (y1 + y3) + (b - b')) =
            ((a - a') * y1 ^ 2 + (b - b') * y1 + (c - c')) -
              ((a - a') * y3 ^ 2 + (b - b') * y3 + (c - c')) := by
          ring
        _ = 0 := hdiff
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hy13)
  have ha_sub : a - a' = 0 := by
    have hprod : (a - a') * (y2 - y3) = 0 := by
      calc
        (a - a') * (y2 - y3) =
            ((a - a') * (y1 + y2) + (b - b')) -
              ((a - a') * (y1 + y3) + (b - b')) := by
          ring
        _ = 0 - 0 := by rw [h12, h13]
        _ = 0 := by simp
    exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hy23)
  have hb_sub : b - b' = 0 := by
    have h := h12
    rw [ha_sub] at h
    simpa using h
  have hc_sub : c - c' = 0 := by
    have h := hz1
    rw [ha_sub, hb_sub] at h
    simpa using h
  exact ⟨sub_eq_zero.mp ha_sub, sub_eq_zero.mp hb_sub, sub_eq_zero.mp hc_sub⟩

end Omega.Zeta
