import Mathlib.Tactic
import Omega.Conclusion.BinfoldTwoScalarCompleteReconstruction
import Omega.Conclusion.LastbitGibbsCriticalTemperatureLogphi

namespace Omega.Conclusion

noncomputable section

/-- The locked physical temperature parameter. -/
def conclusion_physical_temperature_q1_unique_triple_lock_eta_star : ℝ :=
  1 / (1 + Real.goldenRatio ^ 2)

/-- A normalized last-bit Gibbs temperature coordinate used by the existing critical-temperature
wrapper. -/
def conclusion_physical_temperature_q1_unique_triple_lock_lastbit_line (beta : ℝ) : ℝ :=
  1 / (1 + Real.goldenRatio * Real.exp beta)

/-- The escort temperature line, normalized to the integer temperature coordinate. -/
def conclusion_physical_temperature_q1_unique_triple_lock_escort_line (q : ℕ) : ℝ :=
  binfoldEscortTheta Real.goldenRatio q

/-- The third affine invariant of the locked two-point thermal field. -/
def conclusion_physical_temperature_q1_unique_triple_lock_Y_R3 : ℝ :=
  1

/-- The fourth affine invariant of the locked two-point thermal field. -/
def conclusion_physical_temperature_q1_unique_triple_lock_Y_R4 : ℝ :=
  -1

/-- The recorded third affine invariant of the real-input-40 local statistic. -/
def conclusion_physical_temperature_q1_unique_triple_lock_X_R3 : ℝ :=
  21799980451 / 10000000000

/-- The recorded fourth affine invariant of the real-input-40 local statistic. -/
def conclusion_physical_temperature_q1_unique_triple_lock_X_R4 : ℝ :=
  4785762833 / 2000000000

/-- Concrete conclusion package for the q=1 thermal lock: last-bit uniqueness, escort-coordinate
uniqueness, the two-point invariant values, and the recorded noncoincidence with real input 40. -/
def conclusion_physical_temperature_q1_unique_triple_lock_statement : Prop :=
  (∀ beta : ℝ,
      conclusion_physical_temperature_q1_unique_triple_lock_lastbit_line beta =
          conclusion_physical_temperature_q1_unique_triple_lock_eta_star ↔
        beta = Real.log Real.goldenRatio) ∧
    (∀ q : ℕ,
      conclusion_physical_temperature_q1_unique_triple_lock_escort_line q =
          conclusion_physical_temperature_q1_unique_triple_lock_eta_star ↔
        q = 1) ∧
    conclusion_physical_temperature_q1_unique_triple_lock_Y_R3 = 1 ∧
    conclusion_physical_temperature_q1_unique_triple_lock_Y_R4 = -1 ∧
    conclusion_physical_temperature_q1_unique_triple_lock_X_R3 ≠
      conclusion_physical_temperature_q1_unique_triple_lock_Y_R3 ∧
    conclusion_physical_temperature_q1_unique_triple_lock_X_R4 ≠
      conclusion_physical_temperature_q1_unique_triple_lock_Y_R4 ∧
    StrictAnti (binfoldEscortTheta Real.goldenRatio)

/-- Paper label: `cor:conclusion-physical-temperature-q1-unique-triple-lock`. -/
theorem paper_conclusion_physical_temperature_q1_unique_triple_lock :
    conclusion_physical_temperature_q1_unique_triple_lock_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact paper_conclusion_lastbit_gibbs_critical_temperature_logphi
      conclusion_physical_temperature_q1_unique_triple_lock_lastbit_line
      conclusion_physical_temperature_q1_unique_triple_lock_eta_star
      (by
        intro beta
        constructor
        · intro h
          have hden_left :
              (1 + Real.goldenRatio * Real.exp beta : ℝ) ≠ 0 := by positivity
          have hden_right : (1 + Real.goldenRatio ^ 2 : ℝ) ≠ 0 := by positivity
          unfold conclusion_physical_temperature_q1_unique_triple_lock_lastbit_line
            conclusion_physical_temperature_q1_unique_triple_lock_eta_star at h
          have hden_eq :
              1 + Real.goldenRatio * Real.exp beta = 1 + Real.goldenRatio ^ 2 := by
            exact inv_inj.mp (by simpa [one_div] using h)
          have hmul : Real.goldenRatio * Real.exp beta = Real.goldenRatio ^ 2 := by
            linarith
          have hexp : Real.exp beta = Real.goldenRatio := by
            calc
              Real.exp beta = (Real.goldenRatio * Real.exp beta) / Real.goldenRatio := by
                field_simp [Real.goldenRatio_ne_zero]
              _ = Real.goldenRatio ^ 2 / Real.goldenRatio := by rw [hmul]
              _ = Real.goldenRatio := by
                field_simp [Real.goldenRatio_ne_zero]
          exact Real.exp_injective (by
            simpa [Real.exp_log Real.goldenRatio_pos] using hexp)
        · intro h
          subst beta
          unfold conclusion_physical_temperature_q1_unique_triple_lock_lastbit_line
            conclusion_physical_temperature_q1_unique_triple_lock_eta_star
          rw [Real.exp_log Real.goldenRatio_pos]
          ring)
  · intro q
    constructor
    · intro hq
      have hanti : StrictAnti (binfoldEscortTheta Real.goldenRatio) :=
        (paper_conclusion_binfold_two_scalar_complete_reconstruction).2.2.1
      have hq_one :
          binfoldEscortTheta Real.goldenRatio q = binfoldEscortTheta Real.goldenRatio 1 := by
        unfold conclusion_physical_temperature_q1_unique_triple_lock_escort_line
          conclusion_physical_temperature_q1_unique_triple_lock_eta_star at hq
        simpa [binfoldEscortTheta] using hq
      rcases lt_trichotomy q 1 with hlt | heq | hgt
      · have hstrict := hanti hlt
        rw [hq_one] at hstrict
        exact (lt_irrefl _ hstrict).elim
      · exact heq
      · have hstrict := hanti hgt
        rw [hq_one] at hstrict
        exact (lt_irrefl _ hstrict).elim
    · intro hq
      subst hq
      simp [conclusion_physical_temperature_q1_unique_triple_lock_escort_line,
        conclusion_physical_temperature_q1_unique_triple_lock_eta_star, binfoldEscortTheta]
  · rfl
  · rfl
  · norm_num [conclusion_physical_temperature_q1_unique_triple_lock_X_R3,
      conclusion_physical_temperature_q1_unique_triple_lock_Y_R3]
  · norm_num [conclusion_physical_temperature_q1_unique_triple_lock_X_R4,
      conclusion_physical_temperature_q1_unique_triple_lock_Y_R4]
  · exact (paper_conclusion_binfold_two_scalar_complete_reconstruction).2.2.1

end

end Omega.Conclusion
