import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `prop:conclusion-galois-stable-digit-set-attractor-measure-invariance`.
Concrete data for an equivariant finite affine IFS, its attractor fixed point, and its
self-similar measure fixed point. -/
structure conclusion_galois_stable_digit_set_attractor_measure_invariance_data where
  G : Type
  Digit : Type
  Space : Type
  Measure : Type
  pointAction : G → Space → Space
  measureAction : G → Measure → Measure
  digitAction : G → Digit → Digit
  digitAction_surjective : ∀ σ d, ∃ e, digitAction σ e = d
  branch : Digit → Space → Space
  branch_equivariant :
    ∀ σ d x, pointAction σ (branch d x) = branch (digitAction σ d) (pointAction σ x)
  attractor : Set Space
  measure : Measure
  attractor_fixed : {y | ∃ d x, x ∈ attractor ∧ branch d x = y} = attractor
  attractor_unique : ∀ K : Set Space, {y | ∃ d x, x ∈ K ∧ branch d x = y} = K → K = attractor
  measureStep : Measure → Measure
  measure_fixed : measureStep measure = measure
  measure_step_equivariant : ∀ σ μ, measureAction σ (measureStep μ) = measureStep (measureAction σ μ)
  measure_unique : ∀ μ, measureStep μ = μ → μ = measure

abbrev conclusion_galois_stable_digit_set_attractor_measure_invariance_IFSData :=
  conclusion_galois_stable_digit_set_attractor_measure_invariance_data

namespace conclusion_galois_stable_digit_set_attractor_measure_invariance_data

def pointImage
    (D : conclusion_galois_stable_digit_set_attractor_measure_invariance_data)
    (σ : D.G) (K : Set D.Space) : Set D.Space :=
  {y | ∃ x, x ∈ K ∧ D.pointAction σ x = y}

def attractorStep
    (D : conclusion_galois_stable_digit_set_attractor_measure_invariance_data)
    (K : Set D.Space) : Set D.Space :=
  {y | ∃ d x, x ∈ K ∧ D.branch d x = y}

def attractor_invariant
    (D : conclusion_galois_stable_digit_set_attractor_measure_invariance_data) : Prop :=
  ∀ σ, D.pointImage σ D.attractor = D.attractor

def measure_invariant
    (D : conclusion_galois_stable_digit_set_attractor_measure_invariance_data) : Prop :=
  ∀ σ, D.measureAction σ D.measure = D.measure

def galoisInvariantAttractor
    (D : conclusion_galois_stable_digit_set_attractor_measure_invariance_IFSData) : Prop :=
  D.attractor_invariant

def galoisInvariantMeasure
    (D : conclusion_galois_stable_digit_set_attractor_measure_invariance_IFSData) : Prop :=
  D.measure_invariant

lemma attractorStep_pointImage
    (D : conclusion_galois_stable_digit_set_attractor_measure_invariance_data)
    (σ : D.G) (K : Set D.Space) :
    D.attractorStep (D.pointImage σ K) = D.pointImage σ (D.attractorStep K) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨d, z, hz, hzy⟩
    rcases hz with ⟨x, hxK, hxz⟩
    rcases D.digitAction_surjective σ d with ⟨e, he⟩
    refine ⟨D.branch e x, ?_, ?_⟩
    · exact ⟨e, x, hxK, rfl⟩
    · rw [D.branch_equivariant σ e x, he, hxz, hzy]
  · intro hy
    rcases hy with ⟨z, hz, hzy⟩
    rcases hz with ⟨d, x, hxK, hzx⟩
    refine ⟨D.digitAction σ d, D.pointAction σ x, ?_, ?_⟩
    · exact ⟨x, hxK, rfl⟩
    · rw [← D.branch_equivariant σ d x, hzx, hzy]

end conclusion_galois_stable_digit_set_attractor_measure_invariance_data

open conclusion_galois_stable_digit_set_attractor_measure_invariance_data

/-- Paper label: `prop:conclusion-galois-stable-digit-set-attractor-measure-invariance`. -/
theorem paper_conclusion_galois_stable_digit_set_attractor_measure_invariance
    (D : conclusion_galois_stable_digit_set_attractor_measure_invariance_IFSData) :
    D.galoisInvariantAttractor ∧ D.galoisInvariantMeasure := by
  constructor
  · intro σ
    have hfixed : D.attractorStep (D.pointImage σ D.attractor) = D.pointImage σ D.attractor := by
      have hattractor_fixed : D.attractorStep D.attractor = D.attractor := by
        simpa [attractorStep] using D.attractor_fixed
      rw [D.attractorStep_pointImage σ D.attractor, hattractor_fixed]
    exact D.attractor_unique (D.pointImage σ D.attractor) (by
      simpa [attractorStep] using hfixed)
  · intro σ
    have hfixed : D.measureStep (D.measureAction σ D.measure) = D.measureAction σ D.measure := by
      have h := D.measure_step_equivariant σ D.measure
      rw [D.measure_fixed] at h
      exact h.symm
    exact D.measure_unique (D.measureAction σ D.measure) hfixed

end Omega.Conclusion
