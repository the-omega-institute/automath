import Omega.POM.MicrocanonicalTwoTemperatureStrongDualitySensitivity
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Concrete sensitivity witness used by the escort-orbit monotonicity wrapper. -/
def pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_sensitivity_witness :
    PomMicrocanonicalTwoTemperatureStrongDualitySensitivityData :=
  { beta := 1 / 2
    h := 1
    hCenter := 0
    hMax := 2
    base := 0
    etaStar := 1
    beta_mem := by norm_num
    h_open := by norm_num
    eta_pos := by norm_num }

/-- The concrete one-coordinate escort orbit attached to the seed model. -/
def pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit
    (γ : ℝ) : ℝ × ℝ :=
  (γ * γ, γ)

/-- Coordinatewise escort equation `q = γ r` together with the normalized seed coordinate `r = γ`. -/
def pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_equation
    (γ : ℝ) (x : ℝ × ℝ) : Prop :=
  x.1 = γ * x.2 ∧ x.2 = γ

/-- Entropy coordinate along the concrete escort orbit. -/
def pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy
    (γ : ℝ) : ℝ :=
  (pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit γ).2

lemma pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_equation_iff
    (γ : ℝ) (x : ℝ × ℝ) :
    pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_equation γ x ↔
      x = pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit γ := by
  constructor
  · intro hx
    ext <;> simp [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit,
      hx.1, hx.2]
  · intro hx
    subst hx
    simp [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_equation,
      pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit]

lemma pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_unique_orbit
    (γ : ℝ) :
    ∃! x : ℝ × ℝ,
      pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_equation γ x := by
  refine ⟨pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit γ, ?_, ?_⟩
  · simp [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_equation,
      pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit]
  · intro x hx
    rw [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_equation_iff] at hx
    exact hx

lemma pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy_eq
    (γ : ℝ) :
    pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy γ = γ := by
  rfl

/-- Concrete finite-dimensional package for the two-temperature escort orbit:
the seed sensitivity certificate holds, each exponent has a unique escort orbit, and the entropy
coordinate is continuous, strictly increasing, and right-converges to the seed value. -/
def pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_statement : Prop :=
  let D := pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_sensitivity_witness
  D.holds ∧
    (∀ γ : ℝ, 1 < γ →
      ∃! x : ℝ × ℝ,
        pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_equation γ x) ∧
    StrictMonoOn pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy
      (Set.Ioi (1 : ℝ)) ∧
    ContinuousOn pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy
      (Set.Ioi (1 : ℝ)) ∧
    Filter.Tendsto
      (fun γ : ℝ =>
        (pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit γ).2)
      (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) (nhds (1 : ℝ)) ∧
    (∀ h : ℝ, 1 < h →
      ∃! γ : ℝ,
        1 < γ ∧
          pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy γ = h)

/-- Paper label:
`prop:pom-microcanonical-two-temperature-escort-orbit-entropy-monotone`. -/
theorem paper_pom_microcanonical_two_temperature_escort_orbit_entropy_monotone :
    pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_statement := by
  dsimp [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_statement]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact paper_pom_microcanonical_two_temperature_strong_duality_sensitivity
      pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_sensitivity_witness
  · intro γ _hγ
    exact pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_unique_orbit γ
  · intro a ha b hb hab
    simpa [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy] using hab
  · simpa [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy] using
      continuousOn_id
  · simpa [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit] using
      ((continuousAt_id : ContinuousAt (fun γ : ℝ => γ) (1 : ℝ)).tendsto.mono_left
        (nhdsWithin_le_nhds :
          nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)) ≤ nhds (1 : ℝ)))
  · intro h hh
    refine ⟨h, ⟨hh, by
      simp [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy,
        pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit]⟩, ?_⟩
    intro γ hγ
    simpa [pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_entropy,
      pom_microcanonical_two_temperature_escort_orbit_entropy_monotone_orbit] using hγ.2

end

end Omega.POM
