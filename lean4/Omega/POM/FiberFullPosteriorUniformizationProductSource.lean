import Mathlib.Tactic

namespace Omega.POM

/-- The Bernoulli log-odds ratio attached to a single coordinate parameter. -/
noncomputable def posteriorOddsRatio (p : ℝ) : ℝ := p / (1 - p)

/-- The local trigger relation attached to the `100` witness at position `j`. -/
def posteriorUniformTrigger (p : ℕ → ℝ) (j : ℕ) : Prop :=
  posteriorOddsRatio (p j) = posteriorOddsRatio (p (j + 1)) * posteriorOddsRatio (p (j + 2))

/-- Candidate triggers are indexed by the positions where a local `100` block fits. -/
def fullPosteriorUniformizationProductSource (m : ℕ) (p : ℕ → ℝ) : Prop :=
  ∀ j ∈ Finset.range (m - 2), posteriorUniformTrigger p j

/-- The stable word with a single `1` at position `j`. -/
def stableWordSingleOne (m j : ℕ) : Fin m → Bool := fun i => decide (i.1 = j)

lemma stableWordSingleOne_local100 {m j : ℕ} (hj : j + 2 < m) :
    stableWordSingleOne m j ⟨j, by omega⟩ = true ∧
      stableWordSingleOne m j ⟨j + 1, by omega⟩ = false ∧
      stableWordSingleOne m j ⟨j + 2, by omega⟩ = false := by
  unfold stableWordSingleOne
  simp

lemma stableWordSingleOne_hasCandidateTrigger {m j : ℕ} (hj : j + 2 < m) :
    j ∈ Finset.range (m - 2) := by
  apply Finset.mem_range.mpr
  omega

lemma fullPosteriorUniformizationProductSource_iff {m : ℕ} (hm : 3 ≤ m) (p : ℕ → ℝ) :
    fullPosteriorUniformizationProductSource m p ↔
      ∀ j, j + 2 < m → posteriorUniformTrigger p j := by
  constructor
  · intro h j hj
    exact h j (stableWordSingleOne_hasCandidateTrigger hj)
  · intro h j hj
    have hj' : j + 2 < m := by
      have : j < m - 2 := Finset.mem_range.mp hj
      omega
    exact h j hj'

lemma posteriorOddsRatio_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < posteriorOddsRatio p := by
  unfold posteriorOddsRatio
  have hden : 0 < 1 - p := by linarith
  exact div_pos hp0 hden

lemma posteriorOddsRatio_eq_one_iff {p : ℝ} (hp1 : p < 1) :
    posteriorOddsRatio p = 1 ↔ p = 1 / 2 := by
  constructor
  · intro h
    unfold posteriorOddsRatio at h
    have hden : 1 - p ≠ 0 := by linarith
    field_simp [hden] at h
    linarith
  · intro h
    rw [h]
    norm_num [posteriorOddsRatio]

/-- Product Bernoulli sources satisfy full fiberwise posterior uniformization exactly when every
candidate trigger obeys the multiplicative recurrence `a_j = a_{j+1} a_{j+2}`; in the
homogeneous case this forces the fair source `p = 1/2`.
    thm:pom-fiber-full-posterior-uniformization-product-source -/
theorem paper_pom_fiber_full_posterior_uniformization_product_source
    (m : ℕ) (hm : 3 ≤ m) (p : ℕ → ℝ) :
    (fullPosteriorUniformizationProductSource m p ↔
      ∀ j, j + 2 < m → posteriorUniformTrigger p j) ∧
    (∀ q : ℝ, 0 < q → q < 1 →
      (fullPosteriorUniformizationProductSource m (fun _ => q) ↔ q = 1 / 2)) := by
  refine ⟨fullPosteriorUniformizationProductSource_iff hm p, ?_⟩
  intro q hq0 hq1
  rw [fullPosteriorUniformizationProductSource_iff hm (fun _ => q)]
  constructor
  · intro h
    have hwitness := stableWordSingleOne_local100 (m := m) (j := 0) (by omega)
    have h0 := h 0 (by omega)
    have ha_pos : 0 < posteriorOddsRatio q := posteriorOddsRatio_pos hq0 hq1
    have hsquare : posteriorOddsRatio q = posteriorOddsRatio q ^ 2 := by
      simpa [posteriorUniformTrigger, posteriorOddsRatio, pow_two] using h0
    have hone : posteriorOddsRatio q = 1 := by
      nlinarith [ha_pos, hsquare]
    exact (posteriorOddsRatio_eq_one_iff hq1).1 hone
  · intro hq
    intro j hj
    have hone : posteriorOddsRatio q = 1 := (posteriorOddsRatio_eq_one_iff hq1).2 hq
    dsimp [posteriorUniformTrigger]
    rw [hone]
    norm_num

end Omega.POM
