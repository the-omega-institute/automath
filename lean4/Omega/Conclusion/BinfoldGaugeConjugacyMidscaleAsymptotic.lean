import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter

/-- Hardy--Ramanujan leading constant for logarithms of partition numbers. -/
noncomputable def conclusion_binfold_gauge_conjugacy_midscale_asymptotic_partition_constant :
    ℝ :=
  Real.pi * Real.sqrt (2 / 3)

/-- Binfold two-state exponential base. -/
noncomputable def conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda : ℝ :=
  2 / Real.goldenRatio

/-- The midscale normalizing size `(2φ)^(m/2)`. -/
noncomputable def conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale (m : ℕ) :
    ℝ :=
  (2 * Real.goldenRatio) ^ ((m : ℝ) / 2)

/-- The square-root correction from the endpoint with terminal state `1`. -/
noncomputable def conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv :
    ℝ :=
  Real.sqrt Real.goldenRatio⁻¹

/-- The conjugacy-class main coefficient from the partition and Binet main terms. -/
noncomputable def conclusion_binfold_gauge_conjugacy_midscale_asymptotic_constant :
    ℝ :=
  conclusion_binfold_gauge_conjugacy_midscale_asymptotic_partition_constant *
    (Real.goldenRatio / Real.sqrt 5 +
      conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
        (1 / Real.sqrt 5))

/-- Concrete data package for the binfold gauge conjugacy-class midscale asymptotic.

The fields record the partition-number leading term, the two-state square-root multiplicity
decomposition, endpoint counts, Binet main terms, and the two negligible remainders. -/
structure conclusion_binfold_gauge_conjugacy_midscale_asymptotic_data where
  logConjugacy : ℕ → ℝ
  sqrtMultiplicitySum : ℕ → ℝ
  partitionRemainder : ℕ → ℝ
  endpointZeroCount : ℕ → ℝ
  endpointOneCount : ℕ → ℝ
  twoStateError : ℕ → ℝ
  partition_number_asymptotic :
    ∀ m,
      logConjugacy m =
        conclusion_binfold_gauge_conjugacy_midscale_asymptotic_partition_constant *
          sqrtMultiplicitySum m +
          partitionRemainder m
  two_state_binfold_multiplicity_asymptotic :
    ∀ m,
      sqrtMultiplicitySum m =
        endpointZeroCount m *
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^ ((m : ℝ) / 2) +
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
            endpointOneCount m *
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^ ((m : ℝ) / 2) +
          twoStateError m
  endpoint_zero_count :
    ∀ m, endpointZeroCount m = Nat.fib (m + 1)
  endpoint_one_count :
    ∀ m, endpointOneCount m = Nat.fib m
  binet_zero_main :
    Tendsto
      (fun m : ℕ =>
        endpointZeroCount m *
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^ ((m : ℝ) / 2) /
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
      atTop (nhds (Real.goldenRatio / Real.sqrt 5))
  binet_one_main :
    Tendsto
      (fun m : ℕ =>
        endpointOneCount m *
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^ ((m : ℝ) / 2) /
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
      atTop (nhds (1 / Real.sqrt 5))
  two_state_error_negligible :
    Tendsto
      (fun m : ℕ =>
        twoStateError m / conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
      atTop (nhds 0)
  partition_remainder_negligible :
    Tendsto
      (fun m : ℕ =>
        partitionRemainder m /
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
      atTop (nhds 0)

namespace conclusion_binfold_gauge_conjugacy_midscale_asymptotic_data

/-- The paper-facing log-conjugacy asymptotic. -/
def log_conjugacy_main_asymptotic
    (D : conclusion_binfold_gauge_conjugacy_midscale_asymptotic_data) : Prop :=
  Tendsto
    (fun m : ℕ =>
      D.logConjugacy m / conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
    atTop (nhds conclusion_binfold_gauge_conjugacy_midscale_asymptotic_constant)

/-- Paper-facing law name for the conjugacy-class midscale asymptotic. -/
def conclusion_binfold_gauge_conjugacy_midscale_asymptotic_law
    (D : conclusion_binfold_gauge_conjugacy_midscale_asymptotic_data) : Prop :=
  D.log_conjugacy_main_asymptotic

end conclusion_binfold_gauge_conjugacy_midscale_asymptotic_data

/-- Paper label: `thm:conclusion-binfold-gauge-conjugacy-midscale-asymptotic`. -/
theorem paper_conclusion_binfold_gauge_conjugacy_midscale_asymptotic
    (D : conclusion_binfold_gauge_conjugacy_midscale_asymptotic_data) :
    D.conclusion_binfold_gauge_conjugacy_midscale_asymptotic_law := by
  have hOneWeighted :
      Tendsto
        (fun m : ℕ =>
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
            (D.endpointOneCount m *
                conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^
                  ((m : ℝ) / 2) /
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m))
        atTop
        (nhds
          (conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
            (1 / Real.sqrt 5))) := by
    exact D.binet_one_main.const_mul
      conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv
  have hSqrtRaw :
      Tendsto
        (fun m : ℕ =>
          D.endpointZeroCount m *
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^
                ((m : ℝ) / 2) /
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m +
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
            (D.endpointOneCount m *
                conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^
                  ((m : ℝ) / 2) /
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m) +
          D.twoStateError m /
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
        atTop
        (nhds
          (Real.goldenRatio / Real.sqrt 5 +
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
              (1 / Real.sqrt 5) +
            0)) := by
    exact (D.binet_zero_main.add hOneWeighted).add D.two_state_error_negligible
  have hSqrt :
      Tendsto
        (fun m : ℕ =>
          D.sqrtMultiplicitySum m /
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
        atTop
        (nhds
          (Real.goldenRatio / Real.sqrt 5 +
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
              (1 / Real.sqrt 5))) := by
    have hSqrtRaw' :
        Tendsto
          (fun m : ℕ =>
            D.endpointZeroCount m *
                conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^
                  ((m : ℝ) / 2) /
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m +
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
              (D.endpointOneCount m *
                  conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^
                    ((m : ℝ) / 2) /
                conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m) +
            D.twoStateError m /
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
          atTop
          (nhds
            (Real.goldenRatio / Real.sqrt 5 +
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
                (1 / Real.sqrt 5))) := by
      simpa [add_assoc] using hSqrtRaw
    refine hSqrtRaw'.congr' (Filter.Eventually.of_forall fun m => ?_)
    change
      D.endpointZeroCount m *
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^
                ((m : ℝ) / 2) /
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m +
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_sqrt_phi_inv *
            (D.endpointOneCount m *
                conclusion_binfold_gauge_conjugacy_midscale_asymptotic_lambda ^
                  ((m : ℝ) / 2) /
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m) +
          D.twoStateError m /
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m =
        D.sqrtMultiplicitySum m /
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m
    rw [D.two_state_binfold_multiplicity_asymptotic m]
    ring
  have hMain :
      Tendsto
        (fun m : ℕ =>
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_partition_constant *
            (D.sqrtMultiplicitySum m /
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m))
        atTop
        (nhds conclusion_binfold_gauge_conjugacy_midscale_asymptotic_constant) := by
    simpa [conclusion_binfold_gauge_conjugacy_midscale_asymptotic_constant] using
      hSqrt.const_mul
        conclusion_binfold_gauge_conjugacy_midscale_asymptotic_partition_constant
  have hLogRaw :
      Tendsto
        (fun m : ℕ =>
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_partition_constant *
            (D.sqrtMultiplicitySum m /
              conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m) +
          D.partitionRemainder m /
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m)
        atTop
        (nhds conclusion_binfold_gauge_conjugacy_midscale_asymptotic_constant) := by
    simpa using hMain.add D.partition_remainder_negligible
  refine hLogRaw.congr' (Filter.Eventually.of_forall fun m => ?_)
  change
    conclusion_binfold_gauge_conjugacy_midscale_asymptotic_partition_constant *
          (D.sqrtMultiplicitySum m /
            conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m) +
        D.partitionRemainder m /
          conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m =
      D.logConjugacy m / conclusion_binfold_gauge_conjugacy_midscale_asymptotic_scale m
  rw [D.partition_number_asymptotic m]
  ring

end Omega.Conclusion
