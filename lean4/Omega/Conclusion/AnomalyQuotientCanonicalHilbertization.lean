import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- The sharp anomaly representative keeps only components supported on at least two axes. -/
def conclusion_anomaly_quotient_canonical_hilbertization_sharp
    {ι : Type*} (f : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  if S.card ≤ 1 then 0 else f S

/-- The quotient Hilbert norm square is the finite squared norm of the sharp representative. -/
def conclusion_anomaly_quotient_canonical_hilbertization_normSq
    {ι : Type*} [DecidableEq ι] (axes : Finset ι) (f : Finset ι → ℝ) : ℝ :=
  Finset.sum axes.powerset fun S =>
    conclusion_anomaly_quotient_canonical_hilbertization_sharp f S ^ (2 : ℕ)

/-- Paper label: `thm:conclusion-anomaly-quotient-canonical-hilbertization`. -/
theorem paper_conclusion_anomaly_quotient_canonical_hilbertization
    {ι : Type*} [DecidableEq ι] (axes : Finset ι) (f : Finset ι → ℝ) :
    (∀ S ∈ axes.powerset, S.card ≤ 1 →
      conclusion_anomaly_quotient_canonical_hilbertization_sharp f S = 0) ∧
    (∀ S ∈ axes.powerset, 2 ≤ S.card →
      conclusion_anomaly_quotient_canonical_hilbertization_sharp f S = f S) ∧
    conclusion_anomaly_quotient_canonical_hilbertization_normSq axes f =
      Finset.sum (axes.powerset.filter (fun S => 2 ≤ S.card)) fun S => f S ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro S _hS hcard
    simp [conclusion_anomaly_quotient_canonical_hilbertization_sharp, hcard]
  · intro S _hS hcard
    have hnot : ¬ S.card ≤ 1 := by omega
    simp [conclusion_anomaly_quotient_canonical_hilbertization_sharp, hnot]
  · simp only [conclusion_anomaly_quotient_canonical_hilbertization_normSq]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro S _hS
    by_cases hcard : 2 ≤ S.card
    · have hnot : ¬ S.card ≤ 1 := by omega
      simp [conclusion_anomaly_quotient_canonical_hilbertization_sharp, hcard, hnot]
    · have hone : S.card ≤ 1 := by omega
      simp [conclusion_anomaly_quotient_canonical_hilbertization_sharp, hcard, hone]

end

end Omega.Conclusion
