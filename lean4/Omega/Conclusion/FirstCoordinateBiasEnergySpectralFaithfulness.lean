import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite Parseval data for first-coordinate bias energy. -/
structure conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data where
  M : ℕ
  M_pos : 0 < M
  weight : Fin M → ℝ
  fourier : Fin M → ℝ
  multiplicity : Fin M → ℝ
  collision : ℝ
  weight_pos_nonzero : ∀ t : Fin M, t ≠ ⟨0, M_pos⟩ → 0 < weight t
  fourier_zero_iff_uniform :
    (∀ t : Fin M, t ≠ ⟨0, M_pos⟩ → fourier t = 0) ↔
      (∀ r : Fin M, multiplicity r = multiplicity ⟨0, M_pos⟩)
  uniform_iff_collision :
    (∀ r : Fin M, multiplicity r = multiplicity ⟨0, M_pos⟩) ↔
      collision = (1 : ℝ) / (M : ℝ)

namespace conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data

/-- The zero frequency in the cyclic Fourier table. -/
def zeroMode
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) : Fin D.M :=
  ⟨0, D.M_pos⟩

/-- The positive-weight nonzero Fourier contribution to the first-coordinate bias energy. -/
noncomputable def energy
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) : ℝ :=
  ∑ t : Fin D.M, if t = D.zeroMode then 0 else D.weight t * D.fourier t ^ 2

/-- Vanishing of the first-coordinate bias energy. -/
def energyZero
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) : Prop :=
  D.energy = 0

/-- Uniform multiplicity on the residue table. -/
def uniformMultiplicity
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) : Prop :=
  ∀ r : Fin D.M, D.multiplicity r = D.multiplicity D.zeroMode

/-- The baseline collision value `1/M`. -/
def collisionBaseline
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) : Prop :=
  D.collision = (1 : ℝ) / (D.M : ℝ)

lemma energy_term_nonneg
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data)
    (t : Fin D.M) :
    0 ≤ if t = D.zeroMode then 0 else D.weight t * D.fourier t ^ 2 := by
  by_cases ht : t = D.zeroMode
  · simp [ht]
  · exact by
      simp [ht]
      exact mul_nonneg (le_of_lt (D.weight_pos_nonzero t ht)) (sq_nonneg (D.fourier t))

lemma energy_zero_iff_fourier_zero
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) :
    D.energyZero ↔ ∀ t : Fin D.M, t ≠ D.zeroMode → D.fourier t = 0 := by
  constructor
  · intro hEnergy t ht
    have hterms :
        ∀ t : Fin D.M,
          t ∈ Finset.univ →
          (if t = D.zeroMode then 0 else D.weight t * D.fourier t ^ 2) = 0 := by
      have hsum :
          (∑ t : Fin D.M,
              if t = D.zeroMode then 0 else D.weight t * D.fourier t ^ 2) = 0 := by
        simpa [energyZero, energy] using hEnergy
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
            (s := Finset.univ) (f := fun t : Fin D.M =>
              if t = D.zeroMode then 0 else D.weight t * D.fourier t ^ 2)
            (by intro t _; exact D.energy_term_nonneg t)).mp hsum
    have hmul : D.weight t * D.fourier t ^ 2 = 0 := by
      simpa [ht] using hterms t (Finset.mem_univ t)
    have hsq : D.fourier t ^ 2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt (D.weight_pos_nonzero t ht))
    exact sq_eq_zero_iff.mp hsq
  · intro hzero
    rw [energyZero, energy]
    apply Finset.sum_eq_zero
    intro t _
    by_cases ht : t = D.zeroMode
    · simp [ht]
    · simp [ht, hzero t ht]

lemma fourier_zero_iff_uniformMultiplicity
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) :
    (∀ t : Fin D.M, t ≠ D.zeroMode → D.fourier t = 0) ↔ D.uniformMultiplicity := by
  simpa [zeroMode, uniformMultiplicity] using D.fourier_zero_iff_uniform

lemma uniformMultiplicity_iff_collisionBaseline
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) :
    D.uniformMultiplicity ↔ D.collisionBaseline := by
  simpa [zeroMode, uniformMultiplicity, collisionBaseline] using D.uniform_iff_collision

end conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data

/-- Paper label: `thm:conclusion-first-coordinate-bias-energy-spectral-faithfulness`. -/
theorem paper_conclusion_first_coordinate_bias_energy_spectral_faithfulness
    (D : conclusion_first_coordinate_bias_energy_spectral_faithfulness_Data) :
    D.energyZero ↔ D.uniformMultiplicity ∧ D.collisionBaseline := by
  constructor
  · intro hEnergy
    have hFourier :=
      (D.energy_zero_iff_fourier_zero).mp hEnergy
    have hUniform :=
      (D.fourier_zero_iff_uniformMultiplicity).mp hFourier
    exact ⟨hUniform, (D.uniformMultiplicity_iff_collisionBaseline).mp hUniform⟩
  · intro h
    have hFourier :=
      (D.fourier_zero_iff_uniformMultiplicity).mpr h.1
    exact (D.energy_zero_iff_fourier_zero).mpr hFourier

end Omega.Conclusion
