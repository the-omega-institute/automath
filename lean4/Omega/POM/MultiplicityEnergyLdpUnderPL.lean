import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The finite-volume weighted exponential moment, rewritten as a partition-function ratio. -/
def pom_multiplicity_energy_ldp_under_pl_weightedExpectation
    (partitionFunction : ℕ → ℝ → ℝ) (L : ℕ) (t : ℝ) : ℝ :=
  partitionFunction L (1 + t) / partitionFunction L 1

/-- The Legendre-Fenchel transform of the limiting normalized log-mgf on `t > -1`. -/
def pom_multiplicity_energy_ldp_under_pl_legendreRate
    (normalizedLogMgfLimit : ℝ → ℝ) (e : ℝ) : ℝ :=
  sSup
    (Set.range fun t : {t : ℝ // -1 < t} =>
      (t : ℝ) * e - normalizedLogMgfLimit (t : ℝ))

/-- Concrete conclusion: the moment identity, pressure-derived log-mgf, and Legendre rate. -/
def pom_multiplicity_energy_ldp_under_pl_conclusion
    (partitionFunction : ℕ → ℝ → ℝ)
    (lambda normalizedLogMgfLimit rate : ℝ → ℝ) : Prop :=
  (∀ L : ℕ, ∀ t : ℝ,
    pom_multiplicity_energy_ldp_under_pl_weightedExpectation partitionFunction L t =
      partitionFunction L (1 + t) / partitionFunction L 1) ∧
    (∀ t : ℝ,
      -1 < t →
        normalizedLogMgfLimit t = Real.log (lambda (1 + t)) - Real.log (lambda 1)) ∧
      ∀ e : ℝ,
        rate e = pom_multiplicity_energy_ldp_under_pl_legendreRate normalizedLogMgfLimit e

/-- Paper label: `thm:pom-multiplicity-energy-ldp-under-PL`.
The weighted moment is the ratio `Z_L^(1+t)/Z_L^1`; applying the pressure limit at `1+t` and
`1` gives the limiting log-mgf, and the rate is its Legendre-Fenchel transform. -/
theorem paper_pom_multiplicity_energy_ldp_under_pl
    (partitionFunction : ℕ → ℝ → ℝ)
    (pressureLimit lambda normalizedLogMgfLimit rate : ℝ → ℝ)
    (pressureLimit_eval :
      ∀ q : ℝ, 0 < q → pressureLimit q = Real.log (lambda q))
    (logMgfLimit_from_pressure :
      ∀ t : ℝ, -1 < t → normalizedLogMgfLimit t = pressureLimit (1 + t) - pressureLimit 1)
    (rate_formula :
      ∀ e : ℝ,
        rate e = pom_multiplicity_energy_ldp_under_pl_legendreRate normalizedLogMgfLimit e) :
    pom_multiplicity_energy_ldp_under_pl_conclusion
      partitionFunction lambda normalizedLogMgfLimit rate := by
  refine ⟨?_, ?_, ?_⟩
  · intro L t
    rfl
  · intro t ht
    have hq : 0 < 1 + t := by linarith
    have h1 : (0 : ℝ) < 1 := by norm_num
    calc
      normalizedLogMgfLimit t = pressureLimit (1 + t) - pressureLimit 1 := by
        exact logMgfLimit_from_pressure t ht
      _ = Real.log (lambda (1 + t)) - Real.log (lambda 1) := by
        rw [pressureLimit_eval (1 + t) hq, pressureLimit_eval 1 h1]
  · intro e
    exact rate_formula e

end

end Omega.POM
