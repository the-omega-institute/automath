import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-coordinate-bundle-weighted-boundary-exactification`. -/
theorem paper_conclusion_coordinate_bundle_weighted_boundary_exactification
    (ι Edge : Type) [Fintype ι] [DecidableEq ι] [DecidableEq Edge]
    (boundary : ι → Finset Edge) (weight : Edge → ℕ) (choose : ι → Edge)
    (hchoose : ∀ a, choose a ∈ boundary a)
    (hmin : ∀ a e, e ∈ boundary a → weight (choose a) ≤ weight e)
    (hdisj : ∀ a b, a ≠ b → Disjoint (boundary a) (boundary b)) :
    ∃ B : Finset Edge,
      (∀ a, ∃ e ∈ B, e ∈ boundary a) ∧
        (∀ C : Finset Edge, (∀ a, ∃ e ∈ C, e ∈ boundary a) →
          Finset.sum B weight ≤ Finset.sum C weight) ∧
        Finset.sum B weight = ∑ a, weight (choose a) := by
  classical
  let B : Finset Edge := Finset.univ.image choose
  have hchoose_inj :
      ∀ a ∈ (Finset.univ : Finset ι), ∀ b ∈ (Finset.univ : Finset ι),
        choose a = choose b → a = b := by
    intro a _ b _ hab
    by_contra hne
    have hdisj' := hdisj a b hne
    rw [Finset.disjoint_left] at hdisj'
    exact hdisj' (hchoose a) (by simpa [hab] using hchoose b)
  refine ⟨B, ?_, ?_, ?_⟩
  · intro a
    exact ⟨choose a, by simp [B], hchoose a⟩
  · intro C hC
    choose pick hpickC hpickBoundary using hC
    let S : Finset Edge := Finset.univ.image pick
    have hpick_inj :
        ∀ a ∈ (Finset.univ : Finset ι), ∀ b ∈ (Finset.univ : Finset ι),
          pick a = pick b → a = b := by
      intro a _ b _ hab
      by_contra hne
      have hdisj' := hdisj a b hne
      rw [Finset.disjoint_left] at hdisj'
      exact hdisj' (hpickBoundary a) (by simpa [hab] using hpickBoundary b)
    have hBsum : Finset.sum B weight = ∑ a, weight (choose a) := by
      dsimp [B]
      exact Finset.sum_image hchoose_inj
    have hSsum : Finset.sum S weight = ∑ a, weight (pick a) := by
      dsimp [S]
      exact Finset.sum_image hpick_inj
    have hchoose_le_pick : ∑ a : ι, weight (choose a) ≤ ∑ a : ι, weight (pick a) := by
      exact Finset.sum_le_sum fun a _ => hmin a (pick a) (hpickBoundary a)
    have hSsubset : S ⊆ C := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨a, _ha, rfl⟩
      exact hpickC a
    have hS_le_C : Finset.sum S weight ≤ Finset.sum C weight := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hSsubset ?_
      intro e _heC _heS
      exact Nat.zero_le (weight e)
    calc
      Finset.sum B weight = ∑ a : ι, weight (choose a) := hBsum
      _ ≤ ∑ a : ι, weight (pick a) := hchoose_le_pick
      _ = Finset.sum S weight := hSsum.symm
      _ ≤ Finset.sum C weight := hS_le_C
  · dsimp [B]
    exact Finset.sum_image hchoose_inj

end Omega.Conclusion
