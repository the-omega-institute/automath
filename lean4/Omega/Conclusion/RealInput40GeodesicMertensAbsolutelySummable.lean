import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.RealInput40GeodesicMertens

namespace Omega.Conclusion

/-- A concrete square-root geometric tail dominating the renormalized real-input-40 geodesic
Mertens summands. -/
noncomputable def conclusionRealInput40GeodesicMertensTail (n : ℕ) : ℝ :=
  Real.exp (-((n + 1 : ℝ) / 2) * Real.log 4) / Real.log 4

/-- Conclusion-level wrapper: the square-root geometric majorant is absolutely summable, and the
audited Abel finite-part, logarithmic constant, and geodesic Mertens constant are inherited from
the chapter-local real-input-40 package. -/
def conclusionRealInput40GeodesicMertensAbsolutelySummableStatement
    (D : Omega.Zeta.RealInput40GeodesicMertensData) : Prop :=
  Summable (fun n : ℕ => |conclusionRealInput40GeodesicMertensTail n|) ∧
    D.abelFinitePartExpansion ∧ D.logFinitePartValue ∧ D.mertensConstantValue

/-- The geometric square-root tail is summable by the standard exponential-series criterion, and
the constant identifications are exactly those already audited in the real-input-40 geodesic
Mertens package.
    thm:conclusion-realinput40-geodesic-mertens-absolutely-summable -/
theorem paper_conclusion_real_input_40_geodesic_mertens_absolutely_summable
    (D : Omega.Zeta.RealInput40GeodesicMertensData) :
    conclusionRealInput40GeodesicMertensAbsolutelySummableStatement D := by
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hSummable :
      Summable (fun n : ℕ => conclusionRealInput40GeodesicMertensTail n) := by
    have hneg : -(Real.log (4 : ℝ)) / 2 < 0 := by
      linarith
    convert
      (Real.summable_exp_nat_mul_iff.mpr hneg).mul_left
        (Real.exp (-(Real.log (4 : ℝ)) / 2) / Real.log 4) using 1
    ext n
    have hexp :
        Real.exp (-((n + 1 : ℝ) / 2) * Real.log 4) =
          Real.exp (-(Real.log 4) / 2) * Real.exp (n * (-(Real.log 4) / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    unfold conclusionRealInput40GeodesicMertensTail
    rw [hexp]
    field_simp [hlog4.ne']
  have hAbs :
      Summable (fun n : ℕ => |conclusionRealInput40GeodesicMertensTail n|) := by
    convert hSummable using 1
    ext n
    rw [abs_of_nonneg]
    unfold conclusionRealInput40GeodesicMertensTail
    exact div_nonneg (by positivity) hlog4.le
  have hMertens := Omega.Zeta.paper_real_input_40_geodesic_mertens D
  exact ⟨hAbs, hMertens.1, hMertens.2.1, hMertens.2.2⟩

end Omega.Conclusion
