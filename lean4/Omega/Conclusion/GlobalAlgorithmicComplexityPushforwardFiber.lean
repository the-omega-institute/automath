import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-global-algorithmic-complexity-pushforward-fiber`. -/
theorem paper_conclusion_global_algorithmic_complexity_pushforward_fiber
    {Ω X : Type} [DecidableEq X] (S : Finset Ω) (T : Finset X) (F : Ω → X)
    (K : Ω → ℝ) (hT : ∀ ω ∈ S, F ω ∈ T) :
    Finset.sum S K = Finset.sum T (fun x => Finset.sum (S.filter fun ω => F ω = x) K) := by
  classical
  have hfilter : S.filter (fun ω => F ω ∈ T) = S := by
    ext ω
    constructor
    · intro hω
      exact (Finset.mem_filter.mp hω).1
    · intro hω
      exact Finset.mem_filter.mpr ⟨hω, hT ω hω⟩
  have hfiber :=
    Finset.sum_fiberwise_eq_sum_filter (s := S) (t := T) (g := F) (f := K)
  rw [hfilter] at hfiber
  exact hfiber.symm

end Omega.Conclusion
