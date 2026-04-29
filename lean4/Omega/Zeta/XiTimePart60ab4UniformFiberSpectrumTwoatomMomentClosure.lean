import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart60ab4ExactSizebiasPushforwardLaw

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete wrapper for the two-atom uniform fiber-spectrum package. -/
structure xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data where
  pushforwardSeed : xi_time_part60ab4_exact_sizebias_pushforward_law_data
  q : ℕ

namespace xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data

/-- The two limiting masses of the uniform-output fiber spectrum. -/
def xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_mass (b : Bool) : ℝ :=
  cond b ((Real.goldenRatio⁻¹) ^ 2) (Real.goldenRatio⁻¹)

/-- The two limiting support values. -/
def xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_value (b : Bool) : ℝ :=
  cond b (Real.goldenRatio⁻¹) 1

/-- The explicit `q`-moment of the two-atom limit law. -/
def xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_qmoment
    (D : xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data) : ℝ :=
  ∑ b : Bool,
    xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_mass b *
      xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_value b ^ D.q

/-- The asymptotic coefficient appearing in the `S_q^{bin}(m)` main term. -/
def xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_coefficient
    (D : xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data) : ℝ :=
  ((Real.goldenRatio : ℝ) + (Real.goldenRatio⁻¹) ^ D.q) / Real.sqrt 5

/-- Paper-facing wrapper over the previously verified uniform two-state asymptotic and exact
size-bias pushforward law, together with the explicit two-atom `q`-moment and the resulting
closed-form main coefficient. -/
def statement (D : xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data) : Prop :=
  xi_time_part60ab4_exact_sizebias_pushforward_law_statement D.pushforwardSeed ∧
    D.pushforwardSeed.asymptoticSeed.uniform_two_state_asymptotic ∧
    D.xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_qmoment =
      Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹) ^ (D.q + 2) ∧
    D.xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_coefficient =
      ((Real.goldenRatio : ℝ) + (Real.goldenRatio⁻¹) ^ D.q) / Real.sqrt 5

end xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data

open xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data

/-- Paper label: `thm:xi-time-part60ab4-uniform-fiber-spectrum-twoatom-moment-closure`. -/
theorem paper_xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure
    (D : xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_data) : D.statement := by
  have hpush := paper_xi_time_part60ab4_exact_sizebias_pushforward_law D.pushforwardSeed
  have htwo := Omega.Folding.paper_fold_bin_two_state_asymptotic D.pushforwardSeed.asymptoticSeed
  refine ⟨hpush, htwo, ?_, rfl⟩
  simp [xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_qmoment,
    xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_mass,
    xi_time_part60ab4_uniform_fiber_spectrum_twoatom_moment_closure_value, pow_add]
  ring

end

end Omega.Zeta
