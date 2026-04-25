import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `prop:pom-breakpoint-curvature-law-Aq`. -/
theorem paper_pom_breakpoint_curvature_law_aq {q : Nat} (hq : 2 <= q)
    {beta_q beta_q1 gamma_q gamma_q1 A_q L m : Real} (hm : m != 0) (hAq_ne : A_q != 0)
    (hgamma_q : gamma_q = beta_q + L / (m * ((q : Real) - 1)))
    (hgamma_q1 : gamma_q1 = beta_q1 + L / (m * (q : Real)))
    (hcurv : A_q = (q : Real) * ((q : Real) - 1) * (beta_q1 - beta_q)) :
    (gamma_q = gamma_q1 ↔ m = L / A_q) ∧
      A_q = (q : Real) * ((q : Real) - 1) * (beta_q1 - beta_q) := by
  have hm' : m ≠ 0 := by simpa using hm
  have hAq_ne' : A_q ≠ 0 := by simpa using hAq_ne
  have hq_pos : 0 < (q : Real) := by
    exact_mod_cast lt_of_lt_of_le (show 0 < (2 : Nat) by decide) hq
  have hq_gt_one : (1 : Real) < q := by
    exact_mod_cast lt_of_lt_of_le (show 1 < (2 : Nat) by decide) hq
  have hq_sub_pos : 0 < (q : Real) - 1 := by
    linarith
  have hq_ne : (q : Real) ≠ 0 := ne_of_gt hq_pos
  have hq_sub_ne : (q : Real) - 1 ≠ 0 := ne_of_gt hq_sub_pos
  refine ⟨?_, hcurv⟩
  constructor
  · intro hgamma
    have hEq : beta_q + L / (m * ((q : Real) - 1)) = beta_q1 + L / (m * (q : Real)) := by
      rw [← hgamma_q, ← hgamma_q1]
      exact hgamma
    have hmain : m * ((q : Real) * ((q : Real) - 1) * (beta_q1 - beta_q)) = L := by
      have hcleared := hEq
      field_simp [hm', hq_ne, hq_sub_ne] at hcleared
      nlinarith
    have hAm : A_q * m = L := by
      rw [hcurv]
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
    exact (eq_div_iff hAq_ne').2 (by simpa [mul_comm] using hAm)
  · intro hm_eq
    have hAm : m * A_q = L := by
      exact (eq_div_iff hAq_ne').1 hm_eq
    have hmain : m * ((q : Real) * ((q : Real) - 1) * (beta_q1 - beta_q)) = L := by
      rw [hcurv] at hAm
      simpa [mul_assoc, mul_left_comm, mul_comm] using hAm
    rw [hgamma_q, hgamma_q1]
    have hgoal : beta_q + L / (m * ((q : Real) - 1)) =
        beta_q1 + L / (m * (q : Real)) := by
      field_simp [hm', hq_ne, hq_sub_ne]
      nlinarith [hmain]
    exact hgoal

end Omega.POM
