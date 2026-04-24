import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MomentBounds
import Omega.Folding.StableSyntaxCounting

namespace Omega.POM

/-- Explicit lower envelope coming from the Fibonacci-cardinality correction in the cross-`q`
estimate. It is the finite proxy used in the publication wrapper below. -/
noncomputable def pomCrossqGoldenLowerEnvelope (q : ℕ) : ℝ :=
  -Real.log Real.goldenRatio / (2 * q)

/-- Publication-facing cross-`q` package: the finite moment lower bounds hold at the two chosen
orders, the Fibonacci counting identity is available at every resolution, and the explicit golden
lower envelope is monotone in `q`. This is the concrete Lean surrogate used for
`prop:pom-crossq-g-monotone`. -/
def PomCrossqGMonotoneStatement (p q : ℕ) : Prop :=
  2 ≤ p → p ≤ q →
    (∀ m, (2 ^ m) ^ p ≤ Omega.momentSum p m * Nat.fib (m + 2) ^ (p - 1)) ∧
      (∀ m, (2 ^ m) ^ q ≤ Omega.momentSum q m * Nat.fib (m + 2) ^ (q - 1)) ∧
      (∀ m, Fintype.card (Omega.X m) = Nat.fib (m + 2)) ∧
      pomCrossqGoldenLowerEnvelope p ≤ pomCrossqGoldenLowerEnvelope q

/-- Paper label: `prop:pom-crossq-g-monotone`. The existing finite-`q` moment inequality supplies
the two power-mean lower bounds, `|X_m| = F_{m+2}` comes from the stable-syntax counting theorem,
and the explicit golden lower envelope is monotone in the order parameter. -/
theorem paper_pom_crossq_g_monotone (p q : ℕ) : PomCrossqGMonotoneStatement p q := by
  intro hp hpq
  have hp1 : 1 ≤ p := by omega
  have hq1 : 1 ≤ q := by omega
  refine ⟨?_, ?_, Omega.Folding.paper_resolution_folding_stable_syntax_counting, ?_⟩
  · intro m
    exact Omega.momentSum_crossq_from_base p m hp1
  · intro m
    exact Omega.momentSum_crossq_from_base q m hq1
  · dsimp [pomCrossqGoldenLowerEnvelope]
    have hlogphi_nonneg : 0 ≤ Real.log Real.goldenRatio := by
      exact le_of_lt (Real.log_pos Real.one_lt_goldenRatio)
    have hp_nat_pos : 0 < p := by omega
    have hq_nat_pos : 0 < q := by omega
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_nat_pos
    have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
    have hrecip : (1 : ℝ) / q ≤ 1 / p := one_div_le_one_div_of_le hp_pos hpq'
    have hhalf_nonneg : 0 ≤ Real.log Real.goldenRatio / 2 := by positivity
    have hscaled :
        (Real.log Real.goldenRatio / 2) * ((1 : ℝ) / q) ≤
          (Real.log Real.goldenRatio / 2) * ((1 : ℝ) / p) :=
      mul_le_mul_of_nonneg_left hrecip hhalf_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using neg_le_neg hscaled

end Omega.POM
