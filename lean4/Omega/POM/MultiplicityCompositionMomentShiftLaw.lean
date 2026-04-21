import Mathlib
import Omega.POM.MultiplicityCompositionMomentHierarchyRationalGrowth

open Filter Topology

namespace Omega.POM

noncomputable section

/-- The `q`-th moment under the fiber-weight law `P_L`, expressed as the shifted partition ratio
`Z_L^(q+1) / Z_L^(1)` in the audited moment-hierarchy seed model. -/
def pomMultiplicityCompositionFiberMoment (q L : ℕ) : ℝ :=
  pomMomentHierarchyPartition (q + 1) L / pomMomentHierarchyPartition 1 L

/-- Normalized logarithmic growth rate of the fiber-weight moments. -/
def pomMultiplicityCompositionFiberMomentRate (q L : ℕ) : ℝ :=
  (1 / (L : ℝ)) * Real.log (pomMultiplicityCompositionFiberMoment q L)

private lemma partition_pos (q : ℕ) : ∀ L : ℕ, 0 < pomMomentHierarchyPartition q L
  | 0 => by simp [pomMomentHierarchyPartition]
  | 1 => by
      have hweight_pos : 0 < pomMomentHierarchyWeight q := by
        unfold pomMomentHierarchyWeight
        positivity
      simpa [pomMomentHierarchyPartition] using hweight_pos
  | L + 2 => by
      have hweight_pos : 0 < pomMomentHierarchyWeight q := by
        unfold pomMomentHierarchyWeight
        positivity
      have hnext := partition_pos q (L + 1)
      have hcurr := partition_pos q L
      simp [pomMomentHierarchyPartition, hweight_pos, hnext, hcurr, add_pos]

private lemma lambda_pos (q : ℕ) : 0 < pomMomentHierarchyDominantRoot q := by
  have h := paper_pom_multiplicity_composition_moment_hierarchy_rational_growth
  exact (h.2.2.2.1 q).2.2

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:pom-multiplicity-composition-moment-shift-law`.
The fiber-weight expectation of `W_L^q` is exactly the shifted partition ratio
`Z_L^(q+1) / Z_L^(1)`. Any verified exponential growth laws for the numerator and denominator
therefore transfer directly to the normalized logarithmic growth rate of this expectation. -/
theorem paper_pom_multiplicity_composition_moment_shift_law
    (q : ℕ)
    (hNumerator :
      Tendsto (fun L : ℕ => (1 / (L : ℝ)) * Real.log (pomMomentHierarchyPartition (q + 1) L))
        atTop (nhds (Real.log (pomMomentHierarchyDominantRoot (q + 1)))))
    (hDenominator :
      Tendsto (fun L : ℕ => (1 / (L : ℝ)) * Real.log (pomMomentHierarchyPartition 1 L))
        atTop (nhds (Real.log (pomMomentHierarchyDominantRoot 1)))) :
    (∀ L, pomMultiplicityCompositionFiberMoment q L =
      pomMomentHierarchyPartition (q + 1) L / pomMomentHierarchyPartition 1 L) ∧
      Tendsto (pomMultiplicityCompositionFiberMomentRate q) atTop
        (nhds (Real.log (pomMomentHierarchyDominantRoot (q + 1) /
          pomMomentHierarchyDominantRoot 1))) := by
  refine ⟨fun L => rfl, ?_⟩
  have hsub := hNumerator.sub hDenominator
  have hevent :
      (fun L : ℕ => pomMultiplicityCompositionFiberMomentRate q L) =ᶠ[atTop]
        (fun L : ℕ =>
          (1 / (L : ℝ)) * Real.log (pomMomentHierarchyPartition (q + 1) L) -
            (1 / (L : ℝ)) * Real.log (pomMomentHierarchyPartition 1 L)) := by
    filter_upwards [eventually_ge_atTop 1] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hL)
    unfold pomMultiplicityCompositionFiberMomentRate pomMultiplicityCompositionFiberMoment
    rw [Real.log_div (ne_of_gt (partition_pos (q + 1) L)) (ne_of_gt (partition_pos 1 L))]
    field_simp [hL0]
  have htarget :
      Tendsto (fun L : ℕ =>
        (1 / (L : ℝ)) * Real.log (pomMomentHierarchyPartition (q + 1) L) -
          (1 / (L : ℝ)) * Real.log (pomMomentHierarchyPartition 1 L)) atTop
        (nhds (Real.log (pomMomentHierarchyDominantRoot (q + 1) /
          pomMomentHierarchyDominantRoot 1))) := by
    have hconst :
        Real.log (pomMomentHierarchyDominantRoot (q + 1)) - Real.log
            (pomMomentHierarchyDominantRoot 1) =
          Real.log (pomMomentHierarchyDominantRoot (q + 1) / pomMomentHierarchyDominantRoot 1) := by
      rw [Real.log_div (ne_of_gt (lambda_pos (q + 1))) (ne_of_gt (lambda_pos 1))]
    simpa [hconst] using hsub
  exact htarget.congr' hevent.symm

end

end Omega.POM
