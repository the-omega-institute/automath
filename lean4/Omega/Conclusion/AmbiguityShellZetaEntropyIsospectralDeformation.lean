import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-ambiguity-shell-zeta-entropy-isospectral-deformation`. -/
theorem paper_conclusion_ambiguity_shell_zeta_entropy_isospectral_deformation {R : Type*}
    [CommRing R] (N N' z : R) (ν ν' : ℕ) (hν : 0 < ν) (hν' : 0 < ν')
    (hN : N ^ ν = 0) (hN' : N' ^ ν' = 0) :
    (1 - z * N) * (∑ j ∈ Finset.range ν, z ^ j * N ^ j) = 1 ∧
      (1 - z * N') * (∑ j ∈ Finset.range ν', z ^ j * N' ^ j) = 1 := by
  have geom : ∀ x : R, ∀ n : ℕ, (1 - x) * (∑ j ∈ Finset.range n, x ^ j) = 1 - x ^ n := by
    intro x n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        ring
  have block :
      ∀ (M : R) (k : ℕ), 0 < k → M ^ k = 0 →
        (1 - z * M) * (∑ j ∈ Finset.range k, z ^ j * M ^ j) = 1 := by
    intro M k hk hM
    calc
      (1 - z * M) * (∑ j ∈ Finset.range k, z ^ j * M ^ j)
          = (1 - z * M) * (∑ j ∈ Finset.range k, (z * M) ^ j) := by
              congr 1
              refine Finset.sum_congr rfl ?_
              intro j _
              rw [mul_pow]
      _ = 1 - (z * M) ^ k := geom (z * M) k
      _ = 1 := by
          simp [mul_pow, hM]
  exact ⟨block N ν hν hN, block N' ν' hν' hN'⟩

end Omega.Conclusion
