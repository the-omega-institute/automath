import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-scale-entropy-page-threshold`. -/
theorem paper_xi_scale_entropy_page_threshold {n : Nat} (m δ : Fin n → ℝ)
    (hm : ∀ j, 0 < m j) (hδ : ∀ j, 0 < δ j)
    (hS0 : (∑ j, m j * δ j / (1 + δ j)) > (∑ j, m j) / 2) :
    ∃! t : ℝ,
      0 ≤ t ∧ (∑ j, m j * δ j / (t + 1 + δ j)) = (∑ j, m j) / 2 := by
  classical
  let S : ℝ → ℝ := fun t => ∑ j, m j * δ j / (t + 1 + δ j)
  let K : ℝ := (∑ j, m j) / 2
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hS0
  let T : ℝ := ∑ j, δ j
  have hT_nonneg : 0 ≤ T := by
    exact Finset.sum_nonneg fun j _ => (hδ j).le
  have hδ_le_T : ∀ j, δ j ≤ T := by
    intro j
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin n))) (f := δ)
      (fun k _ => (hδ k).le) (by simp)
  have hT_pos : 0 < T := by
    exact Finset.sum_pos (fun k _ => hδ k) hnonempty
  have hcontOn : ContinuousOn S (Set.Icc 0 T) := by
    dsimp [S]
    refine continuousOn_finset_sum Finset.univ ?_
    intro j _hj
    refine continuousOn_const.div ?_ ?_
    · exact ((continuousOn_id.add continuousOn_const).add continuousOn_const)
    · intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hpos : 0 < x + 1 + δ j := by nlinarith [hx0, hδ j]
      exact hpos.ne'
  have hS_T_lt : S T < K := by
    have hterm_lt : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        m j * δ j / (T + 1 + δ j) < m j / 2 := by
      intro j _hj
      have hden_pos : 0 < T + 1 + δ j := by nlinarith [hT_nonneg, hδ j]
      have hfrac_lt : δ j / (T + 1 + δ j) < (1 : ℝ) / 2 := by
        rw [div_lt_iff₀ hden_pos]
        nlinarith [hδ_le_T j]
      have hmul := mul_lt_mul_of_pos_left hfrac_lt (hm j)
      calc
        m j * δ j / (T + 1 + δ j) = m j * (δ j / (T + 1 + δ j)) := by ring
        _ < m j * ((1 : ℝ) / 2) := hmul
        _ = m j / 2 := by ring
    have hsum_lt :
        (∑ j, m j * δ j / (T + 1 + δ j)) < ∑ j, m j / 2 := by
      exact Finset.sum_lt_sum_of_nonempty hnonempty hterm_lt
    have hsum_div : (∑ j, m j / 2) = (∑ j, m j) / 2 := by
      simp [Finset.sum_div]
    simpa [S, K, hsum_div]
      using hsum_lt
  have hS0' : K < S 0 := by
    simpa [S, K, add_comm, add_left_comm, add_assoc] using hS0
  have hex : ∃ t : ℝ, 0 ≤ t ∧ S t = K := by
    have hK_mem : K ∈ Set.Icc (S T) (S 0) := ⟨le_of_lt hS_T_lt, le_of_lt hS0'⟩
    rcases intermediate_value_Icc' hT_nonneg hcontOn hK_mem with ⟨t, htIcc, htEq⟩
    exact ⟨t, htIcc.1, htEq⟩
  rcases hex with ⟨t, ht_nonneg, ht_eq⟩
  refine ⟨t, ⟨ht_nonneg, ht_eq⟩, ?_⟩
  intro u hu
  have hu_eq : S u = K := by
    simpa [S, K] using hu.2
  by_contra htu
  rcases lt_or_gt_of_ne htu with hlt | hgt
  · have hstrict : S t < S u := by
      dsimp [S]
      refine Finset.sum_lt_sum_of_nonempty hnonempty ?_
      intro j _hj
      have hnum_pos : 0 < m j * δ j := mul_pos (hm j) (hδ j)
      have hden_u_pos : 0 < u + 1 + δ j := by nlinarith [hu.1, hδ j]
      have hden_lt : u + 1 + δ j < t + 1 + δ j := by nlinarith
      exact div_lt_div_of_pos_left hnum_pos hden_u_pos hden_lt
    rw [ht_eq, hu_eq] at hstrict
    exact (lt_irrefl K hstrict)
  · have hstrict : S u < S t := by
      dsimp [S]
      refine Finset.sum_lt_sum_of_nonempty hnonempty ?_
      intro j _hj
      have hnum_pos : 0 < m j * δ j := mul_pos (hm j) (hδ j)
      have hden_t_pos : 0 < t + 1 + δ j := by nlinarith [ht_nonneg, hδ j]
      have hden_lt : t + 1 + δ j < u + 1 + δ j := by nlinarith
      exact div_lt_div_of_pos_left hnum_pos hden_t_pos hden_lt
    rw [ht_eq, hu_eq] at hstrict
    exact (lt_irrefl K hstrict)

end Omega.Zeta
