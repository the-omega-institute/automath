import Omega.Zeta.XiReverseKLSingleFrequencyLegendreFenchelClosed

namespace Omega.Zeta

private lemma xi_reversekl_single_frequency_objective_le_supremum_bound
    (alpha t c : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (ht : 0 ≤ t)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    t * c + Real.log (1 - alpha * c ^ 2) ≤ t := by
  have hc0 : 0 ≤ c := hc.1
  have hc1 : c ≤ 1 := hc.2
  have hc_sq_le : c ^ 2 ≤ 1 := by nlinarith
  have harg_pos : 0 < 1 - alpha * c ^ 2 := by
    nlinarith [halpha0, halpha1, hc_sq_le]
  have hlog_le : Real.log (1 - alpha * c ^ 2) ≤ (1 - alpha * c ^ 2) - 1 :=
    Real.log_le_sub_one_of_pos harg_pos
  have hlog_nonpos : Real.log (1 - alpha * c ^ 2) ≤ 0 := by
    nlinarith [hlog_le, halpha0.le, hc_sq_le]
  have htc_le : t * c ≤ t := by
    nlinarith
  linarith

/-- The single-frequency Fenchel envelope is the supremum of the scalar objective over
`c ∈ [0, 1]`, so every admissible `c` satisfies the corresponding sharp inequality with the exact
closed-form value from the parent Legendre-Fenchel theorem.
    cor:xi-reversekl-single-frequency-sharp-fenchel-inequality -/
theorem paper_xi_reversekl_single_frequency_sharp_fenchel_inequality
    (alpha t c : ℝ) (halpha0 : 0 < alpha) (halpha1 : alpha < 1) (ht : 0 ≤ t)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    t * c + Real.log (1 - alpha * c ^ 2) ≤
      if t ≤ 2 * alpha / (1 - alpha) then
        let u : ℝ := Real.sqrt (1 + t ^ 2 / alpha)
        u - 1 + Real.log (2 / (u + 1))
      else
        t + Real.log (1 - alpha) := by
  let S : Set ℝ := (fun x : ℝ => t * x + Real.log (1 - alpha * x ^ 2)) '' Set.Icc (0 : ℝ) 1
  have hS_bdd : BddAbove S := by
    refine ⟨t, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact xi_reversekl_single_frequency_objective_le_supremum_bound alpha t x halpha0 halpha1 ht hx
  calc
    t * c + Real.log (1 - alpha * c ^ 2) ≤ sSup S := by
      exact le_csSup hS_bdd ⟨c, hc, rfl⟩
    _ =
        if t ≤ 2 * alpha / (1 - alpha) then
          let u : ℝ := Real.sqrt (1 + t ^ 2 / alpha)
          u - 1 + Real.log (2 / (u + 1))
        else
          t + Real.log (1 - alpha) := by
            simpa [S] using
              paper_xi_reversekl_single_frequency_legendre_fenchel_closed alpha t halpha0 halpha1 ht

end Omega.Zeta
