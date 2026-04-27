import Mathlib.Analysis.SpecialFunctions.Log.Base
import Omega.Conclusion.PrimeRegister

/-!
# Divisor-lattice sharp phase constant

This module records the formal corollary available from the existing
`paper_godelLift_divisor_lattice_width_bounds` certificate: an optimal bit sequence gives a
pointwise lower bound for every feasible sequence after applying the monotone base-`2` logarithm and
normalizing by `m log₂ m`.
-/

namespace Omega.Conclusion

open Filter

/-- The sharp constant stated in the paper, written in base-`2` logarithms. -/
noncomputable def conclusion_divisor_lattice_sharp_phase_constant_constant : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2 Real.goldenRatio

/-- The normalizing denominator `m log₂ m` for bit-density comparisons. -/
noncomputable def conclusion_divisor_lattice_sharp_phase_constant_normalizer (m : ℕ) : ℝ :=
  (m : ℝ) * Real.logb 2 (m : ℝ)

/-- Base-`2` logarithmic density of a natural-valued certificate sequence. -/
noncomputable def conclusion_divisor_lattice_sharp_phase_constant_bitDensity
    (N : ℕ → ℕ) (m : ℕ) : ℝ :=
  Real.logb 2 (N m : ℝ) / conclusion_divisor_lattice_sharp_phase_constant_normalizer m

/-- The existing optimal binary-width sequence supplied by the divisor-lattice certificate. -/
def conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence (m : ℕ) : ℕ :=
  Nat.log 2 (Nat.fib (m + 2))

private lemma conclusion_divisor_lattice_sharp_phase_constant_normalizer_pos {m : ℕ}
    (hm : 2 ≤ m) :
    0 < conclusion_divisor_lattice_sharp_phase_constant_normalizer m := by
  unfold conclusion_divisor_lattice_sharp_phase_constant_normalizer
  have hm_one : (1 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hm_pos : 0 < (m : ℝ) := lt_trans zero_lt_one hm_one
  have hlog_pos : 0 < Real.logb 2 (m : ℝ) := Real.logb_pos (by norm_num) hm_one
  exact mul_pos hm_pos hlog_pos

private lemma conclusion_divisor_lattice_sharp_phase_constant_bitDensity_mono
    {optimal candidate : ℕ → ℕ}
    (hoptimal_pos : ∀ m, 2 ≤ m → 1 ≤ optimal m)
    (hminimal : ∀ m, 2 ≤ m → optimal m ≤ candidate m) :
    ∀ᶠ m in atTop,
      conclusion_divisor_lattice_sharp_phase_constant_bitDensity optimal m ≤
        conclusion_divisor_lattice_sharp_phase_constant_bitDensity candidate m := by
  filter_upwards [eventually_ge_atTop 2] with m hm
  have hopt_pos_real : 0 < (optimal m : ℝ) := by
    exact_mod_cast hoptimal_pos m hm
  have hle_real : (optimal m : ℝ) ≤ (candidate m : ℝ) := by
    exact_mod_cast hminimal m hm
  have hlog_le :
      Real.logb 2 (optimal m : ℝ) ≤ Real.logb 2 (candidate m : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hopt_pos_real hle_real
  exact div_le_div_of_nonneg_right hlog_le
    (le_of_lt (conclusion_divisor_lattice_sharp_phase_constant_normalizer_pos hm))

/-- Concrete corollary statement for the divisor-lattice sharp phase constant. -/
def conclusion_divisor_lattice_sharp_phase_constant_statement : Prop :=
  conclusion_divisor_lattice_sharp_phase_constant_constant =
      (1 / 2 : ℝ) * Real.logb 2 Real.goldenRatio ∧
    (∀ candidate : ℕ → ℕ,
      (∀ m, 2 ≤ m →
        conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence m ≤ candidate m) →
      ∀ᶠ m in atTop,
        conclusion_divisor_lattice_sharp_phase_constant_bitDensity
            conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence m ≤
          conclusion_divisor_lattice_sharp_phase_constant_bitDensity candidate m) ∧
    (∀ m, 2 ≤ m →
      m / 2 ≤ conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence m ∧
        conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence m ≤ m) ∧
    ∃ optimal : ℕ → ℕ,
      (∀ m,
        optimal m = conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence m) ∧
        ∀ m, 2 ≤ m →
          conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence m ≤ optimal m ∧
            optimal m ≤ m

/-- Paper label: `cor:conclusion-divisor-lattice-sharp-phase-constant`. -/
theorem paper_conclusion_divisor_lattice_sharp_phase_constant :
    conclusion_divisor_lattice_sharp_phase_constant_statement := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro candidate hcandidate
    refine conclusion_divisor_lattice_sharp_phase_constant_bitDensity_mono ?_ hcandidate
    intro m hm
    have hwidth := (paper_godelLift_divisor_lattice_width_bounds m hm).1
    exact le_trans (by omega : 1 ≤ m / 2) hwidth
  · intro m hm
    simpa [conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence] using
      paper_godelLift_divisor_lattice_width_bounds m hm
  · refine ⟨conclusion_divisor_lattice_sharp_phase_constant_optimalBinarySequence, ?_, ?_⟩
    · intro m
      rfl
    · intro m hm
      refine ⟨le_rfl, ?_⟩
      exact (paper_godelLift_divisor_lattice_width_bounds m hm).2

end Omega.Conclusion
