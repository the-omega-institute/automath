import Mathlib.Tactic
import Omega.Conclusion.TqftGenusHausdorffMomentSequence
import Omega.Conclusion.TqftGenusLogconvexity

namespace Omega.Conclusion

open scoped BigOperators

private lemma conclusion_tqft_genus_bound_by_positive_pressure_weighted_cauchy
    {n : ℕ} (mass w : Fin n → ℝ) (hmass : ∀ j, 0 ≤ mass j) :
    (∑ j, mass j * w j) ^ 2 ≤ (∑ j, mass j) * ∑ j, mass j * w j ^ 2 := by
  simpa [pow_two, Real.sq_sqrt, hmass, mul_assoc, mul_left_comm, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := fun j => Real.sqrt (mass j))
      (g := fun j => Real.sqrt (mass j) * w j))

/-- Paper label: `cor:conclusion-tqft-genus-bound-by-positive-pressure`. Finite Cauchy-Schwarz on
the lists `d_m(x)^s` and `d_m(x)^{-s}` yields a lower bound on the genus partition function by the
reciprocal positive-pressure sum. -/
theorem paper_conclusion_tqft_genus_bound_by_positive_pressure
    (D : conclusion_tqft_genus_hausdorff_moment_sequence_data) (g : ℕ) (hg : 2 ≤ g) :
    let s : ℕ := 2 * g - 2
    let S : ℝ := ∑ x : Fin D.n, (D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x : ℝ) ^ s
    (D.n : ℝ) * D.conclusion_tqft_genus_hausdorff_moment_sequence_partition (g - 1) ≥
      (D.n : ℝ) ^ 2 / S := by
  dsimp
  set s : ℕ := 2 * g - 2
  set S : ℝ :=
    ∑ x : Fin D.n, (D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x : ℝ) ^ s
  set mass : Fin D.n → ℝ := fun x =>
    (D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x : ℝ) ^ s
  set w : Fin D.n → ℝ := fun x => (mass x)⁻¹
  have hs : s = 2 * (g - 1) := by
    dsimp [s]
    omega
  have hmass_nonneg : ∀ x, 0 ≤ mass x := by
    intro x
    dsimp [mass]
    positivity
  have hmass_pos : ∀ x, 0 < mass x := by
    intro x
    have hdm_pos : (0 : ℝ) < D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x := by
      exact_mod_cast D.conclusion_tqft_genus_hausdorff_moment_sequence_dm_pos x
    dsimp [mass]
    exact pow_pos hdm_pos s
  have hprod : ∀ x, mass x * w x = 1 := by
    intro x
    dsimp [w]
    field_simp [(hmass_pos x).ne']
  have hwSq : ∀ x, mass x * w x ^ 2 = w x := by
    intro x
    calc
      mass x * w x ^ 2 = (mass x * w x) * w x := by ring
      _ = w x := by rw [hprod x, one_mul]
  have hweighted :=
    conclusion_tqft_genus_bound_by_positive_pressure_weighted_cauchy mass w hmass_nonneg
  have hleft :
      (∑ x : Fin D.n, mass x * w x) = D.n := by
    calc
      (∑ x : Fin D.n, mass x * w x) = ∑ x : Fin D.n, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simp [hprod x]
      _ = D.n := by simp
  have hright :
      ∑ x : Fin D.n, mass x * (w x * w x) = ∑ x : Fin D.n, w x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simpa [pow_two] using hwSq x
  have hcs : (D.n : ℝ) ^ 2 ≤ S * ∑ x : Fin D.n, w x := by
    simpa [S, mass, hleft, hright, pow_two, mul_comm, mul_left_comm, mul_assoc] using hweighted
  have hx0 : Fin D.n := ⟨0, D.conclusion_tqft_genus_hausdorff_moment_sequence_nonempty⟩
  have hS_pos_term : 0 < mass hx0 := hmass_pos hx0
  have hS_nonneg : 0 ≤ S := by
    exact Finset.sum_nonneg fun x hx => hmass_nonneg x
  have hS_term_le : mass hx0 ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum (fun x hx => hmass_nonneg x) (by simp)
  have hS_pos : 0 < S := by
    nlinarith
  have hbound : (D.n : ℝ) ^ 2 / S ≤ ∑ x : Fin D.n, w x := by
    refine (div_le_iff₀ hS_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcs
  have hnode :
      ∀ x : Fin D.n,
        D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ (g - 1) = w x := by
    intro x
    let d : ℝ := D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x
    have hd_pos' : 0 < (D.conclusion_tqft_genus_hausdorff_moment_sequence_dm x : ℝ) := by
      exact_mod_cast D.conclusion_tqft_genus_hausdorff_moment_sequence_dm_pos x
    have hd_pos : 0 < d := by
      simpa [d] using hd_pos'
    have hd_ne : d ≠ 0 := ne_of_gt hd_pos
    have hmul : d⁻¹ * d⁻¹ = (d * d)⁻¹ := by
      field_simp [hd_ne]
    have hnode0 :
        D.conclusion_tqft_genus_hausdorff_moment_sequence_node x = d⁻¹ * d⁻¹ := by
      calc
        D.conclusion_tqft_genus_hausdorff_moment_sequence_node x = (d ^ 2)⁻¹ := by
          simp [conclusion_tqft_genus_hausdorff_moment_sequence_data.conclusion_tqft_genus_hausdorff_moment_sequence_node, d]
        _ = (d * d)⁻¹ := by simp [pow_two]
        _ = d⁻¹ * d⁻¹ := by rw [← hmul]
    calc
      D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ (g - 1) = (d⁻¹ * d⁻¹) ^ (g - 1) := by
        rw [hnode0]
      _ = ((d * d)⁻¹) ^ (g - 1) := by rw [hmul]
      _ = ((d * d) ^ (g - 1))⁻¹ := by rw [inv_pow]
      _ = w x := by
        dsimp [w, mass]
        simp [d, hs, pow_mul, pow_two]
  have hpartition :
      (D.n : ℝ) * D.conclusion_tqft_genus_hausdorff_moment_sequence_partition (g - 1) =
        ∑ x : Fin D.n, w x := by
    have hn_ne : (D.n : ℝ) ≠ 0 := by
      have hn_pos : (0 : ℝ) < D.n := by
        exact_mod_cast D.conclusion_tqft_genus_hausdorff_moment_sequence_nonempty
      linarith
    calc
      (D.n : ℝ) * D.conclusion_tqft_genus_hausdorff_moment_sequence_partition (g - 1) =
          (D.n : ℝ) *
            ((∑ x : Fin D.n,
                D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ (g - 1)) / D.n) := by
            rfl
      _ = ∑ x : Fin D.n, D.conclusion_tqft_genus_hausdorff_moment_sequence_node x ^ (g - 1) := by
            field_simp [hn_ne]
      _ = ∑ x : Fin D.n, w x := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [hnode x]
  rw [hpartition]
  exact hbound

end Omega.Conclusion
