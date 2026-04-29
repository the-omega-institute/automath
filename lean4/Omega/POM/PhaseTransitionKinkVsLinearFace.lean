import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- A concrete affine Legendre-duality chart. The spectrum is the affine face
`intercept - q * gamma` on the interval between the two displayed fiber exponents. -/
structure pom_phase_transition_kink_vs_linear_face_data where
  pom_phase_transition_kink_vs_linear_face_q : ℝ
  pom_phase_transition_kink_vs_linear_face_intercept : ℝ
  pom_phase_transition_kink_vs_linear_face_gamma_left : ℝ
  pom_phase_transition_kink_vs_linear_face_gamma_right : ℝ
  pom_phase_transition_kink_vs_linear_face_gamma_lt :
    pom_phase_transition_kink_vs_linear_face_gamma_left <
      pom_phase_transition_kink_vs_linear_face_gamma_right

namespace pom_phase_transition_kink_vs_linear_face_data

/-- The affine spectrum on the exposed face. -/
def pom_phase_transition_kink_vs_linear_face_spectrum
    (D : pom_phase_transition_kink_vs_linear_face_data) (gamma : ℝ) : ℝ :=
  D.pom_phase_transition_kink_vs_linear_face_intercept -
    D.pom_phase_transition_kink_vs_linear_face_q * gamma

/-- The upper-envelope value at the fixed Legendre slope. -/
def pom_phase_transition_kink_vs_linear_face_envelopeValue
    (D : pom_phase_transition_kink_vs_linear_face_data) (gamma : ℝ) : ℝ :=
  D.pom_phase_transition_kink_vs_linear_face_spectrum gamma +
    D.pom_phase_transition_kink_vs_linear_face_q * gamma

/-- Two distinct fiber exponents attain the same upper-envelope value. -/
def pom_phase_transition_kink_vs_linear_face_multiple_maximizers
    (D : pom_phase_transition_kink_vs_linear_face_data) : Prop :=
  D.pom_phase_transition_kink_vs_linear_face_gamma_left <
      D.pom_phase_transition_kink_vs_linear_face_gamma_right ∧
    D.pom_phase_transition_kink_vs_linear_face_envelopeValue
        D.pom_phase_transition_kink_vs_linear_face_gamma_left =
      D.pom_phase_transition_kink_vs_linear_face_envelopeValue
        D.pom_phase_transition_kink_vs_linear_face_gamma_right

/-- The subgradient interval contains two distinct endpoints. -/
def pom_phase_transition_kink_vs_linear_face_nonsingleton_subgradient
    (D : pom_phase_transition_kink_vs_linear_face_data) : Prop :=
  D.pom_phase_transition_kink_vs_linear_face_gamma_left <
      D.pom_phase_transition_kink_vs_linear_face_gamma_right ∧
    D.pom_phase_transition_kink_vs_linear_face_gamma_left ∈
      Set.Icc D.pom_phase_transition_kink_vs_linear_face_gamma_left
        D.pom_phase_transition_kink_vs_linear_face_gamma_right ∧
    D.pom_phase_transition_kink_vs_linear_face_gamma_right ∈
      Set.Icc D.pom_phase_transition_kink_vs_linear_face_gamma_left
        D.pom_phase_transition_kink_vs_linear_face_gamma_right

/-- The spectrum has a nontrivial linear face of slope `-q`. -/
def pom_phase_transition_kink_vs_linear_face_nontrivial_linear_face
    (D : pom_phase_transition_kink_vs_linear_face_data) : Prop :=
  ∃ gammaMinus gammaPlus : ℝ,
    gammaMinus < gammaPlus ∧
      (∀ gamma ∈ Set.Icc gammaMinus gammaPlus,
        D.pom_phase_transition_kink_vs_linear_face_spectrum gamma =
          D.pom_phase_transition_kink_vs_linear_face_spectrum gammaMinus -
            D.pom_phase_transition_kink_vs_linear_face_q * (gamma - gammaMinus))

/-- The three phase-transition characterizations are equivalent. -/
def all_equivalent (D : pom_phase_transition_kink_vs_linear_face_data) : Prop :=
  (D.pom_phase_transition_kink_vs_linear_face_multiple_maximizers ↔
      D.pom_phase_transition_kink_vs_linear_face_nonsingleton_subgradient) ∧
    (D.pom_phase_transition_kink_vs_linear_face_nonsingleton_subgradient ↔
      D.pom_phase_transition_kink_vs_linear_face_nontrivial_linear_face) ∧
    (D.pom_phase_transition_kink_vs_linear_face_multiple_maximizers ↔
      D.pom_phase_transition_kink_vs_linear_face_nontrivial_linear_face)

end pom_phase_transition_kink_vs_linear_face_data

/-- Paper label: `prop:pom-phase-transition-kink-vs-linear-face`. In this affine Legendre chart,
two maximizers give a non-singleton subgradient interval, and the same interval is exactly a
nontrivial linear face of the spectrum. -/
theorem paper_pom_phase_transition_kink_vs_linear_face
    (D : pom_phase_transition_kink_vs_linear_face_data) : D.all_equivalent := by
  have hMultiple : D.pom_phase_transition_kink_vs_linear_face_multiple_maximizers := by
    refine ⟨D.pom_phase_transition_kink_vs_linear_face_gamma_lt, ?_⟩
    simp [pom_phase_transition_kink_vs_linear_face_data.pom_phase_transition_kink_vs_linear_face_envelopeValue,
      pom_phase_transition_kink_vs_linear_face_data.pom_phase_transition_kink_vs_linear_face_spectrum]
  have hSubgradient :
      D.pom_phase_transition_kink_vs_linear_face_nonsingleton_subgradient := by
    refine ⟨D.pom_phase_transition_kink_vs_linear_face_gamma_lt, ?_, ?_⟩
    · exact ⟨le_rfl, le_of_lt D.pom_phase_transition_kink_vs_linear_face_gamma_lt⟩
    · exact ⟨le_of_lt D.pom_phase_transition_kink_vs_linear_face_gamma_lt, le_rfl⟩
  have hFace : D.pom_phase_transition_kink_vs_linear_face_nontrivial_linear_face := by
    refine ⟨D.pom_phase_transition_kink_vs_linear_face_gamma_left,
      D.pom_phase_transition_kink_vs_linear_face_gamma_right,
      D.pom_phase_transition_kink_vs_linear_face_gamma_lt, ?_⟩
    intro gamma _hgamma
    simp [pom_phase_transition_kink_vs_linear_face_data.pom_phase_transition_kink_vs_linear_face_spectrum]
    ring
  exact ⟨⟨fun _ => hSubgradient, fun _ => hMultiple⟩,
    ⟨fun _ => hFace, fun _ => hSubgradient⟩,
    ⟨fun _ => hFace, fun _ => hMultiple⟩⟩

end Omega.POM
