import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open Filter Topology

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-lowtemp-pressure-germ-dual-recovery`. -/
theorem paper_conclusion_lowtemp_pressure_germ_dual_recovery
    (aStar rhoStar Delta C₁ C₂ C₃ : ℝ) (P massOutside tvErr : ℕ → ℝ) (hDelta : 0 < Delta)
    (hP : ∀ q,
      |P q - ((q : ℝ) * Real.log aStar + Real.log rhoStar)| ≤ C₁ * Real.exp (-Delta * q))
    (hMass : ∀ q, massOutside q ≤ C₂ * Real.exp (-Delta * q))
    (hTV : ∀ q, tvErr q ≤ C₃ * Real.exp (-Delta * q)) :
    Tendsto (fun q => P q / q) atTop (𝓝 (Real.log aStar)) ∧
      Tendsto (fun q => P q - (q : ℝ) * Real.log aStar) atTop (𝓝 (Real.log rhoStar)) := by
  let _ := hMass
  let _ := hTV
  let err : ℕ → ℝ := fun q => P q - ((q : ℝ) * Real.log aStar + Real.log rhoStar)
  have hExp :
      Tendsto (fun q : ℕ => C₁ * Real.exp (-Delta * (q : ℝ))) atTop (𝓝 0) := by
    have hlin : Tendsto (fun q : ℕ => (-Delta : ℝ) * (q : ℝ)) atTop atBot := by
      have hpos : Tendsto (fun q : ℕ => Delta * (q : ℝ)) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hDelta
      have hneg : Tendsto (fun q : ℕ => -(Delta * (q : ℝ))) atTop atBot :=
        tendsto_neg_atTop_atBot.comp hpos
      simpa [neg_mul] using hneg
    simpa using (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hlin))
  have hErrAbs : Tendsto (fun q : ℕ => |err q|) atTop (𝓝 0) := by
    refine squeeze_zero (fun q => abs_nonneg _) ?_ hExp
    intro q
    simpa [err] using hP q
  have hErr : Tendsto err atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 hErrAbs
  have hInterceptAux :
      Tendsto (fun q : ℕ => err q + Real.log rhoStar) atTop (𝓝 (0 + Real.log rhoStar)) :=
    hErr.add tendsto_const_nhds
  have hIntercept :
      Tendsto (fun q : ℕ => P q - (q : ℝ) * Real.log aStar) atTop (𝓝 (Real.log rhoStar)) := by
    have hEq :
        (fun q : ℕ => P q - (q : ℝ) * Real.log aStar) =
          fun q : ℕ => err q + Real.log rhoStar := by
      funext q
      simp [err]
      ring
    rw [hEq]
    simpa using hInterceptAux
  have hErrDivAbs : Tendsto (fun q : ℕ => |err q / (q : ℝ)|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun q => abs_nonneg _) ?_ hExp
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    have hq_one : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc
      |err q / (q : ℝ)| = |err q| / (q : ℝ) := by rw [abs_div, abs_of_nonneg hq_nonneg]
      _ ≤ |err q| := by exact div_le_self (abs_nonneg _) hq_one
      _ ≤ C₁ * Real.exp (-Delta * (q : ℝ)) := by simpa [err] using hP q
  have hErrDiv : Tendsto (fun q : ℕ => err q / (q : ℝ)) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 hErrDivAbs
  have hLogDiv : Tendsto (fun q : ℕ => Real.log rhoStar / (q : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log rhoStar)
  have hSlopeAux :
      Tendsto
        (fun q : ℕ => Real.log aStar + err q / (q : ℝ) + Real.log rhoStar / (q : ℝ))
        atTop
        (𝓝 (Real.log aStar)) := by
    simpa [add_assoc] using ((tendsto_const_nhds.add hErrDiv).add hLogDiv)
  have hSlopeEq :
      (fun q : ℕ => P q / (q : ℝ)) =ᶠ[atTop]
        (fun q : ℕ => Real.log aStar + err q / (q : ℝ) + Real.log rhoStar / (q : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with q hq
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    simp [err]
    field_simp [hq0]
    ring
  have hSlope : Tendsto (fun q : ℕ => P q / (q : ℝ)) atTop (𝓝 (Real.log aStar)) :=
    Tendsto.congr' hSlopeEq.symm hSlopeAux
  exact ⟨hSlope, hIntercept⟩

end Omega.Conclusion
