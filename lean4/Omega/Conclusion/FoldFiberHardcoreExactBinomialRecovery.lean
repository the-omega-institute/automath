import Omega.Conclusion.FoldFiberHardcoreAnnealedConservation

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-fold-fiber-hardcore-exact-binomial-recovery`. -/
theorem paper_conclusion_fold_fiber_hardcore_exact_binomial_recovery
    (m : ℕ) {X : Type*} [Fintype X] [DecidableEq X] (p s t : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (hs : 0 < s) (ht : t = p / (1 - p)) (fold : FoldSubset m → X)
    (oneCount : X → ℕ) (reward : FoldSubset m → ℕ)
    (hsplit : ∀ ω : FoldSubset m, ω.card = oneCount (fold ω) + reward ω) :
    (1 - p) ^ m *
        (∑ x : X, (t * s) ^ oneCount x * foldFiberPartition fold reward (t * s) x) =
      (1 - p + p * s) ^ m := by
  have hpden : 0 < 1 - p := by linarith
  have htpos : 0 < t := by
    rw [ht]
    exact div_pos hp0 hpden
  have hactivity : 0 < t * s := mul_pos htpos hs
  have hglobal :
      (∑ x : X, (t * s) ^ oneCount x * foldFiberPartition fold reward (t * s) x) =
        (1 + t * s) ^ m :=
    (paper_conclusion_fold_fiber_hardcore_annealed_conservation
      m (t * s) hactivity fold oneCount reward hsplit).2.2
  rw [hglobal]
  calc
    (1 - p) ^ m * (1 + t * s) ^ m = ((1 - p) * (1 + t * s)) ^ m := by
      rw [mul_pow]
    _ = (1 - p + p * s) ^ m := by
      congr 1
      rw [ht]
      field_simp [hpden.ne']

end Omega.Conclusion
