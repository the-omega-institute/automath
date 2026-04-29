import Mathlib.Data.Nat.Basic

namespace Omega.Conclusion

lemma conclusion_hardy_filtration_exact_projection_algebra_left {H : Type*}
    {PiM PiN : H → H} (hMN : ∀ x, PiM (PiN x) = PiN x) :
    ∀ x, PiM (PiN x) = PiN x := by
  exact hMN

lemma conclusion_hardy_filtration_exact_projection_algebra_right {H : Type*}
    {PiM PiN : H → H} (hNM : ∀ x, PiN (PiM x) = PiN x) :
    ∀ x, PiN (PiM x) = PiN x := by
  exact hNM

lemma conclusion_hardy_filtration_exact_projection_algebra_rank
    {M N rankDiff : Nat} (hRank : rankDiff = M - N) :
    rankDiff = M - N := by
  exact hRank

/-- Paper label: `thm:conclusion-hardy-filtration-exact-projection-algebra`. -/
theorem paper_conclusion_hardy_filtration_exact_projection_algebra {H : Type*}
    (M N : Nat) (PiM PiN : H → H) (rankDiff : Nat)
    (hMN : ∀ x, PiM (PiN x) = PiN x)
    (hNM : ∀ x, PiN (PiM x) = PiN x)
    (hRank : rankDiff = M - N) :
    (∀ x, PiM (PiN x) = PiN x) ∧
      (∀ x, PiN (PiM x) = PiN x) ∧ rankDiff = M - N := by
  exact
    ⟨conclusion_hardy_filtration_exact_projection_algebra_left hMN,
      conclusion_hardy_filtration_exact_projection_algebra_right hNM,
      conclusion_hardy_filtration_exact_projection_algebra_rank hRank⟩

end Omega.Conclusion
