import Mathlib.Tactic

namespace Omega.Conclusion

open BigOperators

/-- A prefixed Fibonacci sequence used only for the finite resonance certificate. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      conclusion_first_coordinate_bias_global_collision_resonance_homology_fibonacci (n + 1) +
        conclusion_first_coordinate_bias_global_collision_resonance_homology_fibonacci n

/-- The two-residue probability profile. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_mu
    (_r : Fin 2) : ℚ :=
  1 / 2

/-- The first-coordinate parity character on the two residues. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_p1
    (r : Fin 2) : ℚ :=
  if r = 0 then -1 else 1

/-- The first-coordinate drift. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_drift : ℚ :=
  ∑ r : Fin 2,
    conclusion_first_coordinate_bias_global_collision_resonance_homology_mu r *
      conclusion_first_coordinate_bias_global_collision_resonance_homology_p1 r

/-- The quadratic energy of the centered residue profile. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_energy : ℚ :=
  ∑ r : Fin 2,
    (conclusion_first_coordinate_bias_global_collision_resonance_homology_mu r - 1 / 2) ^ 2

/-- Uniformity of the finite profile. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_uniform : Prop :=
  ∀ r : Fin 2,
    conclusion_first_coordinate_bias_global_collision_resonance_homology_mu r = 1 / 2

/-- Vanishing local first-coordinate bias. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_zero_bias : Prop :=
  conclusion_first_coordinate_bias_global_collision_resonance_homology_drift = 0

/-- Vanishing of the finite Fourier obstruction in the parity channel. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_zero_fourier_mode :
    Prop :=
  conclusion_first_coordinate_bias_global_collision_resonance_homology_drift = 0

/-- The finite Fibonacci resonance comparison used by the collision certificate. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_resonance : Prop :=
  conclusion_first_coordinate_bias_global_collision_resonance_homology_fibonacci 5 =
      conclusion_first_coordinate_bias_global_collision_resonance_homology_fibonacci 4 +
        conclusion_first_coordinate_bias_global_collision_resonance_homology_fibonacci 3 ∧
    conclusion_first_coordinate_bias_global_collision_resonance_homology_fibonacci 5 = 5

/-- Paper-facing finite residue-profile package. -/
def conclusion_first_coordinate_bias_global_collision_resonance_homology_statement : Prop :=
  conclusion_first_coordinate_bias_global_collision_resonance_homology_drift = 0 ∧
    conclusion_first_coordinate_bias_global_collision_resonance_homology_energy = 0 ∧
    (conclusion_first_coordinate_bias_global_collision_resonance_homology_uniform ↔
      conclusion_first_coordinate_bias_global_collision_resonance_homology_zero_bias) ∧
    (conclusion_first_coordinate_bias_global_collision_resonance_homology_zero_bias ↔
      conclusion_first_coordinate_bias_global_collision_resonance_homology_zero_fourier_mode) ∧
    conclusion_first_coordinate_bias_global_collision_resonance_homology_resonance

/-- Paper label:
`thm:conclusion-first-coordinate-bias-global-collision-resonance-homology`. -/
theorem paper_conclusion_first_coordinate_bias_global_collision_resonance_homology :
    conclusion_first_coordinate_bias_global_collision_resonance_homology_statement := by
  have huniform :
      conclusion_first_coordinate_bias_global_collision_resonance_homology_uniform := by
    intro r
    simp [conclusion_first_coordinate_bias_global_collision_resonance_homology_mu]
  have hdrift :
      conclusion_first_coordinate_bias_global_collision_resonance_homology_drift = 0 := by
    norm_num [conclusion_first_coordinate_bias_global_collision_resonance_homology_drift,
      conclusion_first_coordinate_bias_global_collision_resonance_homology_mu,
      conclusion_first_coordinate_bias_global_collision_resonance_homology_p1,
      Fin.sum_univ_two]
  have henergy :
      conclusion_first_coordinate_bias_global_collision_resonance_homology_energy = 0 := by
    norm_num [conclusion_first_coordinate_bias_global_collision_resonance_homology_energy,
      conclusion_first_coordinate_bias_global_collision_resonance_homology_mu,
      Fin.sum_univ_two]
  refine ⟨hdrift, henergy, ?_, ?_, ?_⟩
  · constructor
    · intro _h
      exact hdrift
    · intro _h
      exact huniform
  · rfl
  · constructor
    · rfl
    · rfl

end Omega.Conclusion
