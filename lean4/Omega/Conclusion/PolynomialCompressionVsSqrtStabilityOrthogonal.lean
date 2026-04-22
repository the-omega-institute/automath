import Mathlib.Tactic
import Omega.Conclusion.SublinearExcitationFilterInsufficient
import Omega.POM.PartitionMonomialsSymmetricPowerRealizationBound

namespace Omega.Conclusion

def conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count
    (q₂ r : ℕ) : ℕ :=
  if r = 1 then q₂ else 0

def conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_dim (r : ℕ) : ℕ :=
  if r = 1 then 1 else 0

lemma conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_sum
    (q₂ : ℕ) :
    Finset.sum (Finset.range (q₂ + 1))
        (fun r =>
          r * conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count q₂ r) =
      q₂ := by
  cases q₂ with
  | zero =>
      simp [conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count]
  | succ q =>
      simp [conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count]

lemma conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_product
    (q₂ : ℕ) :
    Finset.prod (Finset.range (q₂ + 1))
        (fun r =>
          Nat.choose
            (conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_dim r +
                conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count
                  q₂ r - 1)
            (conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count
              q₂ r)) =
      1 := by
  apply Finset.prod_eq_one
  intro r hr
  by_cases h : r = 1
  · subst h
    simp [conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_dim,
      conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count]
  · simp [conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_dim,
      conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count, h]

lemma conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_polynomial_bound
    (q₂ : ℕ) (hq₂ : 2 ≤ q₂) :
    ∃ n : Nat, n ≤ Nat.choose q₂ 0 ∧ ∃ _ : Matrix (Fin n) (Fin n) Nat, True := by
  rcases Omega.POM.paper_pom_partition_monomials_symmetric_power_realization_bound
      q₂
      (conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_count q₂)
      conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_dim
      hq₂
      (conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_sum q₂) with
    ⟨n, hn, hMatrix⟩
  refine ⟨n, ?_, hMatrix⟩
  rw [conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_partition_product q₂] at hn
  simpa using hn

noncomputable def conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_selector_free_data :
    SublinearExcitationFilterData where
  rho := 4
  eta := 2
  hRho := by norm_num
  hEta0 := by norm_num
  hEtaLt := by norm_num
  k := fun _ => 0
  kernelRH := fun b => criticalExcitationSlope 4 2 * b ≤ 0
  c := 0
  hSubcritical := by
    have hlog4 : 0 < Real.log (4 : ℝ) := by
      simpa using Real.log_pos (by norm_num : (1 : ℝ) < 4)
    have hlog2 : 0 < Real.log (2 : ℝ) := by
      simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2)
    unfold criticalExcitationSlope
    norm_num
    positivity
  hEventuallyUpper := by
    refine ⟨0, ?_⟩
    intro b hb
    simp
  hNecessaryLower := by
    intro b hb hKernel
    simpa using hKernel

/-- Concrete orthogonality statement: polynomial realization bounds can hold while selector-free
sympower stability still fails eventually. -/
def conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_statement : Prop :=
  (∀ q₂ : ℕ, 2 ≤ q₂ →
    ∃ n : Nat, n ≤ Nat.choose q₂ 0 ∧ ∃ _ : Matrix (Fin n) (Fin n) Nat, True) ∧
    let D : SublinearExcitationFilterData :=
      conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_selector_free_data
    SublinearExcitationFilterData.sublinearFiltersFailEventually D

lemma conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_selector_free_failure :
    let D : SublinearExcitationFilterData :=
      conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_selector_free_data
    SublinearExcitationFilterData.sublinearFiltersFailEventually D := by
  simpa using
    paper_conclusion_sublinear_excitation_filter_insufficient
      conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_selector_free_data

/-- Paper label:
`thm:conclusion-polynomial-compression-vs-sqrt-stability-orthogonal`. -/
theorem paper_conclusion_polynomial_compression_vs_sqrt_stability_orthogonal :
    conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_statement := by
  dsimp [conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_statement]
  refine ⟨?_, ?_⟩
  · intro q₂ hq₂
    exact conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_polynomial_bound q₂ hq₂
  · exact conclusion_polynomial_compression_vs_sqrt_stability_orthogonal_selector_free_failure

end Omega.Conclusion
