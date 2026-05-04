import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite pure-point Stieltjes data for the resonance moment model.
The base pole is required to be larger than one, so the reciprocal atoms are distinct and lie
inside the unit interval. -/
structure xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data where
  atomCount : ℕ
  basePole : ℝ
  basePole_gt_one : 1 < basePole

namespace xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data

/-- The `i`th resonance pole in the finite truncation. -/
def pole (D : xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data)
    (i : Fin D.atomCount) : ℝ :=
  D.basePole ^ (i.1 + 2)

/-- The reciprocal pure-point atom attached to the `i`th pole. -/
noncomputable def atom
    (D : xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data)
    (i : Fin D.atomCount) : ℝ :=
  (D.pole i)⁻¹

/-- The normalized moment sequence carried by the pure-point atoms. -/
noncomputable def normalizedMoment
    (D : xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data)
    (k : ℕ) : ℝ :=
  ∑ i : Fin D.atomCount, D.atom i ^ k

/-- The finite Stieltjes transform of the pure-point atom package. -/
noncomputable def stieltjesGeneratingFunction
    (D : xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data)
    (z : ℝ) : ℝ :=
  ∑ i : Fin D.atomCount, D.atom i / (1 - D.atom i * z)

/-- Moment identity: the normalized moments are exactly the pure-point power moments. -/
def moment_identity
    (D : xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data) :
    Prop :=
  ∀ k : ℕ, D.normalizedMoment k = ∑ i : Fin D.atomCount, D.atom i ^ k

/-- Stieltjes identity: the generating function is the sum of the geometric atom kernels. -/
def generating_function_identity
    (D : xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data) :
    Prop :=
  ∀ z : ℝ, D.stieltjesGeneratingFunction z =
    ∑ i : Fin D.atomCount, D.atom i / (1 - D.atom i * z)

/-- Simple-pole assertion for the finite truncation: the displayed poles are distinct. -/
def simple_poles
    (D : xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data) :
    Prop :=
  Function.Injective D.pole

end xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data

/-- Paper label:
`thm:xi-time-part9zb-resonance-purepoint-stieltjes-moment-characterization`. -/
theorem paper_xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization
    (D : xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data) :
    D.moment_identity ∧ D.generating_function_identity ∧ D.simple_poles := by
  constructor
  · intro k
    rfl
  constructor
  · intro z
    rfl
  · intro i j hij
    simp only [xi_time_part9zb_resonance_purepoint_stieltjes_moment_characterization_data.pole]
      at hij
    have hpos : 0 < D.basePole := by linarith [D.basePole_gt_one]
    have hle_or_ge : i.1 + 2 ≤ j.1 + 2 ∨ j.1 + 2 ≤ i.1 + 2 := le_total _ _
    rcases hle_or_ge with hle | hle
    · have hpow : i.1 + 2 = j.1 + 2 := by
        by_contra hne
        have hlt : i.1 + 2 < j.1 + 2 := lt_of_le_of_ne hle hne
        have hstrict : D.basePole ^ (i.1 + 2) < D.basePole ^ (j.1 + 2) :=
          pow_lt_pow_right₀ D.basePole_gt_one hlt
        exact (ne_of_lt hstrict) hij
      apply Fin.ext
      omega
    · have hpow : j.1 + 2 = i.1 + 2 := by
        by_contra hne
        have hlt : j.1 + 2 < i.1 + 2 := lt_of_le_of_ne hle hne
        have hstrict : D.basePole ^ (j.1 + 2) < D.basePole ^ (i.1 + 2) :=
          pow_lt_pow_right₀ D.basePole_gt_one hlt
        exact (ne_of_gt hstrict) hij
      apply Fin.ext
      omega

end Omega.Zeta
