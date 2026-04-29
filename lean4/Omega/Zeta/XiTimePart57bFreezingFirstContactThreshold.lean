import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.FoldPressureFreezingThreshold
import Omega.Zeta.XiTimePart57bPressureSpectrumDiscreteConvexityMonotoneExcess

namespace Omega.Zeta

open Omega.Folding

/-- Concrete threshold data for the first freezing contact of the part57b excess profile. The
pressure spectrum comes from the existing monotone-excess package, while one extra affine upper
branch and one integer level above the critical threshold force an exact contact with the ground
state line. -/
structure XiTimePart57bFreezingFirstContactThresholdData where
  spectrum : XiTimePart57bPressureSpectrumDiscreteConvexityData
  alphaTwo : ℝ
  witnessLevel : ℕ
  hgap : alphaTwo < spectrum.alphaStar
  hUpper :
    ∀ a : ℕ,
      spectrum.P a ≤
        max ((a : ℝ) * spectrum.alphaStar + spectrum.gStar)
          ((a : ℝ) * alphaTwo + Real.log Real.goldenRatio)
  hThreshold :
    (Real.log Real.goldenRatio - spectrum.gStar) / (spectrum.alphaStar - alphaTwo) < witnessLevel

namespace XiTimePart57bFreezingFirstContactThresholdData

/-- The part57b excess profile `E_a = P_a - a α_*`. -/
def xi_time_part57b_freezing_first_contact_threshold_excess
    (D : XiTimePart57bFreezingFirstContactThresholdData) (a : ℕ) : ℝ :=
  D.spectrum.excess a

private lemma xi_time_part57b_freezing_first_contact_threshold_witness_value
    (D : XiTimePart57bFreezingFirstContactThresholdData) :
    D.xi_time_part57b_freezing_first_contact_threshold_excess D.witnessLevel = D.spectrum.gStar := by
  have hpackage := paper_xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess D.spectrum
  have hlower :
      ∀ n : ℕ, (n : ℝ) * D.spectrum.alphaStar + D.spectrum.gStar ≤ D.spectrum.P n := by
    intro n
    have hbounds := (hpackage.2.2 n).1
    unfold XiTimePart57bPressureSpectrumDiscreteConvexityData.excess at hbounds
    linarith
  have hpressure :
      D.spectrum.P D.witnessLevel =
        (D.witnessLevel : ℝ) * D.spectrum.alphaStar + D.spectrum.gStar := by
    simpa using
      paper_fold_pressure_freezing_threshold D.spectrum.P D.spectrum.alphaStar D.alphaTwo
        D.spectrum.gStar D.witnessLevel D.hgap hlower D.hUpper D.hThreshold
  unfold xi_time_part57b_freezing_first_contact_threshold_excess
    XiTimePart57bPressureSpectrumDiscreteConvexityData.excess
  linarith

private lemma xi_time_part57b_freezing_first_contact_threshold_contact_exists
    (D : XiTimePart57bFreezingFirstContactThresholdData) :
    ∃ a : ℕ, D.xi_time_part57b_freezing_first_contact_threshold_excess a = D.spectrum.gStar :=
  ⟨D.witnessLevel, D.xi_time_part57b_freezing_first_contact_threshold_witness_value⟩

/-- Minimal integer contact level where the part57b excess hits the frozen value `g_*`. -/
noncomputable def xi_time_part57b_freezing_first_contact_threshold_firstContactIndex
    (D : XiTimePart57bFreezingFirstContactThresholdData) : ℕ :=
  Nat.find D.xi_time_part57b_freezing_first_contact_threshold_contact_exists

/-- The frozen value is attained at the first-contact level. -/
def firstContactExists (D : XiTimePart57bFreezingFirstContactThresholdData) : Prop :=
  D.xi_time_part57b_freezing_first_contact_threshold_excess
      D.xi_time_part57b_freezing_first_contact_threshold_firstContactIndex =
    D.spectrum.gStar

/-- The first contact occurs no later than the explicit witness level above the critical threshold. -/
def firstContactBound (D : XiTimePart57bFreezingFirstContactThresholdData) : Prop :=
  D.xi_time_part57b_freezing_first_contact_threshold_firstContactIndex ≤ D.witnessLevel

/-- Once the excess reaches `g_*`, monotonicity and the lower ground-state bound force every later
integer level to remain frozen. -/
def tailFrozen (D : XiTimePart57bFreezingFirstContactThresholdData) : Prop :=
  ∀ a : ℕ,
    D.xi_time_part57b_freezing_first_contact_threshold_firstContactIndex ≤ a →
      D.xi_time_part57b_freezing_first_contact_threshold_excess a = D.spectrum.gStar

end XiTimePart57bFreezingFirstContactThresholdData

open XiTimePart57bFreezingFirstContactThresholdData

private lemma xi_time_part57b_freezing_first_contact_threshold_tail_le
    (D : XiTimePart57bFreezingFirstContactThresholdData) :
    ∀ {a b : ℕ},
      a ≤ b →
        D.xi_time_part57b_freezing_first_contact_threshold_excess b ≤
          D.xi_time_part57b_freezing_first_contact_threshold_excess a := by
  intro a b hab
  have hpackage := paper_xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess D.spectrum
  induction hab with
  | refl =>
      simp
  | @step b hab ih =>
      have hstep :
          D.xi_time_part57b_freezing_first_contact_threshold_excess (b + 1) ≤
            D.xi_time_part57b_freezing_first_contact_threshold_excess b := by
        simpa [xi_time_part57b_freezing_first_contact_threshold_excess] using hpackage.2.1 b
      exact le_trans hstep ih

/-- Paper label: `cor:xi-time-part57b-freezing-first-contact-threshold`. An integer level above the
critical affine threshold already satisfies `E_a = g_*`; taking the minimal such index with
`Nat.find` and combining excess monotonicity with the universal lower bound `g_* ≤ E_a` freezes
the entire tail. -/
theorem paper_xi_time_part57b_freezing_first_contact_threshold
    (D : XiTimePart57bFreezingFirstContactThresholdData) :
    D.firstContactExists ∧ D.firstContactBound ∧ D.tailFrozen := by
  have hpackage := paper_xi_time_part57b_pressure_spectrum_discrete_convexity_monotone_excess D.spectrum
  refine ⟨?_, ?_, ?_⟩
  · unfold XiTimePart57bFreezingFirstContactThresholdData.firstContactExists
      xi_time_part57b_freezing_first_contact_threshold_firstContactIndex
    exact Nat.find_spec D.xi_time_part57b_freezing_first_contact_threshold_contact_exists
  · unfold XiTimePart57bFreezingFirstContactThresholdData.firstContactBound
      xi_time_part57b_freezing_first_contact_threshold_firstContactIndex
    exact Nat.find_min'
      D.xi_time_part57b_freezing_first_contact_threshold_contact_exists
      D.xi_time_part57b_freezing_first_contact_threshold_witness_value
  · intro a ha
    have hle :
        D.xi_time_part57b_freezing_first_contact_threshold_excess a ≤
          D.xi_time_part57b_freezing_first_contact_threshold_excess
            D.xi_time_part57b_freezing_first_contact_threshold_firstContactIndex :=
      xi_time_part57b_freezing_first_contact_threshold_tail_le D ha
    have hlow : D.spectrum.gStar ≤ D.xi_time_part57b_freezing_first_contact_threshold_excess a :=
      (hpackage.2.2 a).1
    have hcontact :
        D.xi_time_part57b_freezing_first_contact_threshold_excess
            D.xi_time_part57b_freezing_first_contact_threshold_firstContactIndex =
          D.spectrum.gStar := by
      unfold xi_time_part57b_freezing_first_contact_threshold_firstContactIndex
      exact Nat.find_spec D.xi_time_part57b_freezing_first_contact_threshold_contact_exists
    linarith

end Omega.Zeta
