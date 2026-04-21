import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Omega.Folding

/-- Paper label: `prop:fold-gauge-anomaly-bernoulli-p-bayes-phase-transition`. -/
theorem paper_fold_gauge_anomaly_bernoulli_p_bayes_phase_transition :
    ∃! pC : Real, pC ∈ Set.Ioo 0 1 ∧ pC ^ 4 - 3 * pC ^ 3 + 3 * pC ^ 2 + pC - 1 = 0 ∧
      pC ^ 2 * (3 - 2 * pC) / (1 + pC ^ 3) = 1 - pC := by
  let f : Real → Real := fun p => p + (p ^ 4 + (-1 + (p ^ 2 * 3 + -(p ^ 3 * 3))))
  have hf_cont : Continuous f := by
    continuity
  have hzero_mem : (0 : Real) ∈ Set.Ioo (f 0) (f 1) := by
    dsimp [f]
    norm_num
  rcases intermediate_value_Ioo (show (0 : Real) ≤ 1 by norm_num) hf_cont.continuousOn hzero_mem with
    ⟨pC, hpC, hpRoot⟩
  have hpRoot' : pC ^ 4 - 3 * pC ^ 3 + 3 * pC ^ 2 + pC - 1 = 0 := by
    simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using hpRoot
  refine ⟨pC, ?_, ?_⟩
  · refine ⟨hpC, hpRoot', ?_⟩
    have hden : (1 + pC ^ 3 : Real) ≠ 0 := by
      nlinarith [hpC.1, hpC.2]
    rw [div_eq_iff hden]
    nlinarith [hpRoot']
  · intro q hq
    rcases hq with ⟨hqIoo, hqRoot, _⟩
    have hf_strict : StrictMonoOn f (Set.Icc (0 : Real) 1) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc (0 : Real) 1) ?_ ?_
      · exact hf_cont.continuousOn
      · intro x hx
        have hx' : x ∈ Set.Ioo (0 : Real) 1 := by
          simpa using hx
        have hderiv : deriv f x = 4 * x ^ 3 - 9 * x ^ 2 + 6 * x + 1 := by
          let hRaw :=
            (((((hasDerivAt_pow 4 x).sub ((hasDerivAt_pow 3 x).const_mul 3)).add
              ((hasDerivAt_pow 2 x).const_mul 3)).add (hasDerivAt_id x)).sub
              (hasDerivAt_const x (1 : Real)))
          have hHas : HasDerivAt f (4 * x ^ 3 - 9 * x ^ 2 + 6 * x + 1) x := by
            convert hRaw using 1
            · ext p
              dsimp [f]
              ring_nf
            · ring
          exact hHas.deriv
        rw [hderiv]
        have hx0 : 0 ≤ x := le_of_lt hx'.1
        have hx1 : x ≤ 1 := le_of_lt hx'.2
        nlinarith
    exact
      (hf_strict.injOn ⟨le_of_lt hpC.1, le_of_lt hpC.2⟩
        ⟨le_of_lt hqIoo.1, le_of_lt hqIoo.2⟩ (hpRoot.trans (by
          simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
            mul_comm] using hqRoot.symm))).symm

end Omega.Folding
