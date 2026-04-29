import Mathlib
import Omega.Folding.KilloFoldBinEscortRenyiLogisticGeometry
import Omega.Zeta.XiFoldEscortLogMultiplicityTwoAtom

namespace Omega.Conclusion

noncomputable section

/-- Bounded continuous test functions used in the paper-facing two-point functional calculus. -/
def conclusion_escort_thermodynamics_two_point_functional_calculus_test_function
    (F : ℝ → ℝ) : Prop :=
  Continuous F ∧ ∃ C : ℝ, ∀ y : ℝ, |F y| ≤ C

/-- The limiting two-point law obtained from the escort last-bit parameter `θ(q)`. -/
def conclusion_escort_thermodynamics_two_point_functional_calculus_law (q : ℝ) : Bool → ℝ :=
  Omega.Zeta.xiFoldEscortLogMultiplicityLaw q

/-- The positive-sign version of the two support points `{0, log φ}`. -/
def conclusion_escort_thermodynamics_two_point_functional_calculus_value : Bool → ℝ
  | false => 0
  | true => Real.log Real.goldenRatio

/-- Expectation against the explicit two-point escort limit law. -/
def conclusion_escort_thermodynamics_two_point_functional_calculus_expectation
    (q : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑ b, conclusion_escort_thermodynamics_two_point_functional_calculus_law q b *
    F (conclusion_escort_thermodynamics_two_point_functional_calculus_value b)

/-- Paper-facing package for the escort thermodynamic two-point calculus. -/
def conclusion_escort_thermodynamics_two_point_functional_calculus_statement (q : ℝ) : Prop :=
  0 < Omega.Folding.killoEscortTheta q ∧
    Omega.Folding.killoEscortTheta q < 1 ∧
    Omega.Folding.killoEscortTheta q = 1 / (1 + Real.goldenRatio ^ (q + 1)) ∧
    (∀ F : ℝ → ℝ,
      conclusion_escort_thermodynamics_two_point_functional_calculus_test_function F →
        conclusion_escort_thermodynamics_two_point_functional_calculus_expectation q F =
          (Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1))) * F 0 +
            (1 / (1 + Real.goldenRatio ^ (q + 1))) * F (Real.log Real.goldenRatio)) ∧
    ∀ t : ℝ,
      conclusion_escort_thermodynamics_two_point_functional_calculus_expectation q
          (fun y => Real.exp (t * y)) =
        (Real.goldenRatio ^ (q + 1) + Real.goldenRatio ^ t) / (1 + Real.goldenRatio ^ (q + 1)) ∧
        Real.log
            (conclusion_escort_thermodynamics_two_point_functional_calculus_expectation q
              (fun y => Real.exp (t * y))) =
          Real.log ((Real.goldenRatio ^ (q + 1) + Real.goldenRatio ^ t) /
            (1 + Real.goldenRatio ^ (q + 1)))

private lemma conclusion_escort_thermodynamics_two_point_functional_calculus_exp_log
    (t : ℝ) : Real.exp (t * Real.log Real.goldenRatio) = Real.goldenRatio ^ t := by
  rw [show t * Real.log Real.goldenRatio = Real.log Real.goldenRatio * t by ring]
  symm
  rw [Real.rpow_def_of_pos Real.goldenRatio_pos]

/-- Paper label: `thm:conclusion-escort-thermodynamics-two-point-functional-calculus`. The escort
thermodynamic limit is the explicit two-point law on `{0, log φ}` with Bernoulli weight
`θ(q) = 1 / (1 + φ^(q+1))`, so bounded continuous observables and the limiting
cumulant-generating function are obtained by direct two-atom evaluation. -/
theorem paper_conclusion_escort_thermodynamics_two_point_functional_calculus
    (q : Real) (hq : 0 <= q) :
    conclusion_escort_thermodynamics_two_point_functional_calculus_statement q := by
  have _ := hq
  have hTwoAtom := Omega.Zeta.paper_xi_fold_escort_log_multiplicity_two_atom q
  have htheta :
      Omega.Folding.killoEscortTheta q = 1 / (1 + Real.goldenRatio ^ (q + 1)) := by
    simpa [Omega.Zeta.xiFoldEscortLogMultiplicityLaw] using hTwoAtom.2.1
  have hlaw_false :
      conclusion_escort_thermodynamics_two_point_functional_calculus_law q false =
        Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1)) := by
    simpa [conclusion_escort_thermodynamics_two_point_functional_calculus_law] using hTwoAtom.1
  have hlaw_true :
      conclusion_escort_thermodynamics_two_point_functional_calculus_law q true =
        1 / (1 + Real.goldenRatio ^ (q + 1)) := by
    simpa [conclusion_escort_thermodynamics_two_point_functional_calculus_law] using hTwoAtom.2.1
  have htheta_pos : 0 < Omega.Folding.killoEscortTheta q := Omega.Folding.killoEscortTheta_pos q
  have htheta_lt_one : Omega.Folding.killoEscortTheta q < 1 :=
    Omega.Folding.killoEscortTheta_lt_one q
  refine ⟨htheta_pos, htheta_lt_one, htheta, ?_, ?_⟩
  · intro F hF
    rcases hF with ⟨_, _⟩
    calc
      conclusion_escort_thermodynamics_two_point_functional_calculus_expectation q F =
          conclusion_escort_thermodynamics_two_point_functional_calculus_law q false * F 0 +
            conclusion_escort_thermodynamics_two_point_functional_calculus_law q true *
              F (Real.log Real.goldenRatio) := by
            simp [conclusion_escort_thermodynamics_two_point_functional_calculus_expectation,
              conclusion_escort_thermodynamics_two_point_functional_calculus_law,
              conclusion_escort_thermodynamics_two_point_functional_calculus_value,
              add_comm]
      _ = (Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1))) * F 0 +
            (1 / (1 + Real.goldenRatio ^ (q + 1))) * F (Real.log Real.goldenRatio) := by
            rw [hlaw_false, hlaw_true]
  · intro t
    have hden : (1 + Real.goldenRatio ^ (q + 1) : ℝ) ≠ 0 := by positivity
    have hmgf :
        conclusion_escort_thermodynamics_two_point_functional_calculus_expectation q
            (fun y => Real.exp (t * y)) =
          (Real.goldenRatio ^ (q + 1) + Real.goldenRatio ^ t) / (1 + Real.goldenRatio ^ (q + 1)) := by
      calc
        conclusion_escort_thermodynamics_two_point_functional_calculus_expectation q
            (fun y => Real.exp (t * y)) =
            conclusion_escort_thermodynamics_two_point_functional_calculus_law q false +
              conclusion_escort_thermodynamics_two_point_functional_calculus_law q true *
                Real.goldenRatio ^ t := by
                simp [conclusion_escort_thermodynamics_two_point_functional_calculus_expectation,
                  conclusion_escort_thermodynamics_two_point_functional_calculus_law,
                  conclusion_escort_thermodynamics_two_point_functional_calculus_value,
                  add_comm,
                  conclusion_escort_thermodynamics_two_point_functional_calculus_exp_log]
        _ = Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1)) +
              (1 / (1 + Real.goldenRatio ^ (q + 1))) * Real.goldenRatio ^ t := by
              rw [hlaw_false, hlaw_true]
        _ = (Real.goldenRatio ^ (q + 1) + Real.goldenRatio ^ t) /
              (1 + Real.goldenRatio ^ (q + 1)) := by
              field_simp [hden]
    exact ⟨hmgf, congrArg Real.log hmgf⟩

end

end Omega.Conclusion
