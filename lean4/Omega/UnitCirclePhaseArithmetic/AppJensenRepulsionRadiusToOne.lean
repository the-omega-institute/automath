import Mathlib.Tactic
import Omega.TypedAddressBiaxialCompletion.JensenCountableCriterion
import Omega.UnitCirclePhaseArithmetic.AppJensenSingleZeroLowerBound

open Filter

namespace Omega.UnitCirclePhaseArithmetic

open Omega.TypedAddressBiaxialCompletion
open JensenCountableCriterionData

/-- Paper label: `cor:app-jensen-repulsion-radius-to-one`. If a cofinal sequence of radii has
repulsion subdisks whose radii tend to `1`, then any hypothetical disk zero would eventually lie
inside one of those zero-free subdisks, which is impossible. Hence the chapter-local RH predicate
holds. -/
theorem paper_app_jensen_repulsion_radius_to_one
    (D : JensenCountableCriterionData) (roots : Finset ℂ)
    (hdefect :
      ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → D.defect ρ = appSingleZeroJensenDefect ρ roots)
    (hdiskZero : ¬ D.rh → ∃ a : ℂ, a ∈ roots ∧ 0 < ‖a‖ ∧ ‖a‖ < 1)
    (hrstar :
      ∃ ρseq : ℕ → ℝ,
        Monotone ρseq ∧
          Tendsto ρseq atTop (nhds 1) ∧
            (∀ n : ℕ, 0 < ρseq n ∧ ρseq n < 1) ∧
              Tendsto
                (fun n : ℕ =>
                  ρseq n * Real.exp (-(D.defect (ρseq n))))
                atTop (nhds 1)) :
    D.rh := by
  rcases hrstar with ⟨ρseq, _hmono, _hρtend, hρmem, hrstar_tend⟩
  by_contra hnotRh
  rcases hdiskZero hnotRh with ⟨a, ha_mem, ha_pos, ha_unit⟩
  have hlarge :
      ∀ᶠ n : ℕ in atTop,
        ‖a‖ < ρseq n * Real.exp (-(D.defect (ρseq n))) := by
    exact hrstar_tend (Ioi_mem_nhds ha_unit)
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hlarge
  have hρn := hρmem n
  have hdef_nonneg : 0 ≤ D.defect (ρseq n) := (D.semantics (ρseq n) hρn.1 hρn.2).1
  have hexp_le_one : Real.exp (-(D.defect (ρseq n))) ≤ 1 := by
    have hneg : -(D.defect (ρseq n)) ≤ 0 := by linarith
    simpa using Real.exp_le_one_iff.mpr hneg
  have hrstar_le_rho : ρseq n * Real.exp (-(D.defect (ρseq n))) ≤ ρseq n := by
    have hρn_nonneg : 0 ≤ ρseq n := le_of_lt hρn.1
    calc
      ρseq n * Real.exp (-(D.defect (ρseq n))) ≤ ρseq n * 1 :=
        mul_le_mul_of_nonneg_left hexp_le_one hρn_nonneg
      _ = ρseq n := by ring
  have ha_lt_rho : ‖a‖ < ρseq n := lt_of_lt_of_le hn hrstar_le_rho
  have hLower :
      Real.log (ρseq n / ‖a‖) ≤ D.defect (ρseq n) := by
    calc
      Real.log (ρseq n / ‖a‖) ≤ appSingleZeroJensenDefect (ρseq n) roots :=
        (paper_app_jensen_single_zero_lower_bound roots ha_mem ha_pos ha_unit).1
          (ρseq n) ha_lt_rho hρn.2
      _ = D.defect (ρseq n) := by symm; exact hdefect hρn.1 hρn.2
  have hExp : ρseq n / ‖a‖ ≤ Real.exp (D.defect (ρseq n)) := by
    have hdiv_pos : 0 < ρseq n / ‖a‖ := div_pos hρn.1 ha_pos
    calc
      ρseq n / ‖a‖ = Real.exp (Real.log (ρseq n / ‖a‖)) := by rw [Real.exp_log hdiv_pos]
      _ ≤ Real.exp (D.defect (ρseq n)) := Real.exp_le_exp.mpr hLower
  have hRhoLe : ρseq n ≤ ‖a‖ * Real.exp (D.defect (ρseq n)) := by
    have := (div_le_iff₀ ha_pos).mp hExp
    simpa [mul_comm] using this
  have hsubdisk : ρseq n * Real.exp (-(D.defect (ρseq n))) ≤ ‖a‖ := by
    have hDiv : ρseq n / Real.exp (D.defect (ρseq n)) ≤ ‖a‖ := by
      refine (div_le_iff₀ (Real.exp_pos (D.defect (ρseq n)))).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hRhoLe
    simpa [Real.exp_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hDiv
  exact (not_lt_of_ge hsubdisk) hn

end Omega.UnitCirclePhaseArithmetic
