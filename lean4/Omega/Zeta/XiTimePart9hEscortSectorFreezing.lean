import Mathlib

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-layer escort data for
`thm:xi-time-part9h-escort-sector-freezing`. -/
structure xi_time_part9h_escort_sector_freezing_data where
  xi_time_part9h_escort_sector_freezing_card : ℕ → ℕ
  xi_time_part9h_escort_sector_freezing_weight :
    ∀ m, Fin (xi_time_part9h_escort_sector_freezing_card m) → ℝ
  xi_time_part9h_escort_sector_freezing_maxWeight : ℕ → ℝ
  xi_time_part9h_escort_sector_freezing_secondWeight : ℕ → ℝ
  xi_time_part9h_escort_sector_freezing_sector :
    ∀ m, Fin (xi_time_part9h_escort_sector_freezing_card m) → Bool
  xi_time_part9h_escort_sector_freezing_maxIndex :
    ∀ m, Fin (xi_time_part9h_escort_sector_freezing_card m)
  xi_time_part9h_escort_sector_freezing_weight_nonneg :
    ∀ m x, 0 ≤ xi_time_part9h_escort_sector_freezing_weight m x
  xi_time_part9h_escort_sector_freezing_max_pos :
    ∀ m, 0 < xi_time_part9h_escort_sector_freezing_maxWeight m
  xi_time_part9h_escort_sector_freezing_maxIndex_spec :
    ∀ m,
      xi_time_part9h_escort_sector_freezing_weight m
          (xi_time_part9h_escort_sector_freezing_maxIndex m) =
        xi_time_part9h_escort_sector_freezing_maxWeight m
  xi_time_part9h_escort_sector_freezing_second_nonneg :
    ∀ m, 0 ≤ xi_time_part9h_escort_sector_freezing_secondWeight m
  xi_time_part9h_escort_sector_freezing_second_bounds_complement :
    ∀ m x,
      xi_time_part9h_escort_sector_freezing_weight m x ≠
          xi_time_part9h_escort_sector_freezing_maxWeight m →
        xi_time_part9h_escort_sector_freezing_weight m x ≤
          xi_time_part9h_escort_sector_freezing_secondWeight m
  xi_time_part9h_escort_sector_freezing_max_sector :
    ∀ m x,
      xi_time_part9h_escort_sector_freezing_weight m x =
          xi_time_part9h_escort_sector_freezing_maxWeight m →
        xi_time_part9h_escort_sector_freezing_sector m x = true
  xi_time_part9h_escort_sector_freezing_asymptotic_bound :
    ∀ qseq : ℕ → ℕ,
      Tendsto qseq atTop atTop →
        Tendsto
          (fun m : ℕ =>
            (xi_time_part9h_escort_sector_freezing_card m : ℝ) *
                xi_time_part9h_escort_sector_freezing_secondWeight m ^ qseq m /
              xi_time_part9h_escort_sector_freezing_maxWeight m ^ qseq m)
          atTop (𝓝 0)

namespace xi_time_part9h_escort_sector_freezing_data

def xi_time_part9h_escort_sector_freezing_denominator
    (D : xi_time_part9h_escort_sector_freezing_data) (m q : ℕ) : ℝ :=
  ∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
    D.xi_time_part9h_escort_sector_freezing_weight m x ^ q

def xi_time_part9h_escort_sector_freezing_sectorBadMass
    (D : xi_time_part9h_escort_sector_freezing_data) (m q : ℕ) : ℝ :=
  (∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
      if D.xi_time_part9h_escort_sector_freezing_sector m x = false then
        D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
      else
        0) /
    D.xi_time_part9h_escort_sector_freezing_denominator m q

def xi_time_part9h_escort_sector_freezing_outsideMaxMass
    (D : xi_time_part9h_escort_sector_freezing_data) (m q : ℕ) : ℝ :=
  (∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
      if D.xi_time_part9h_escort_sector_freezing_weight m x ≠
          D.xi_time_part9h_escort_sector_freezing_maxWeight m then
        D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
      else
        0) /
    D.xi_time_part9h_escort_sector_freezing_denominator m q

def xi_time_part9h_escort_sector_freezing_explicitBound
    (D : xi_time_part9h_escort_sector_freezing_data) (m q : ℕ) : ℝ :=
  (D.xi_time_part9h_escort_sector_freezing_card m : ℝ) *
      D.xi_time_part9h_escort_sector_freezing_secondWeight m ^ q /
    D.xi_time_part9h_escort_sector_freezing_maxWeight m ^ q

def xi_time_part9h_escort_sector_freezing_claim
    (D : xi_time_part9h_escort_sector_freezing_data) : Prop :=
  (∀ m q,
    D.xi_time_part9h_escort_sector_freezing_sectorBadMass m q ≤
        D.xi_time_part9h_escort_sector_freezing_outsideMaxMass m q ∧
      D.xi_time_part9h_escort_sector_freezing_outsideMaxMass m q ≤
        D.xi_time_part9h_escort_sector_freezing_explicitBound m q) ∧
    ∀ qseq : ℕ → ℕ,
      Tendsto qseq atTop atTop →
        Tendsto
          (fun m : ℕ =>
            1 - D.xi_time_part9h_escort_sector_freezing_sectorBadMass m (qseq m))
          atTop (𝓝 1)

end xi_time_part9h_escort_sector_freezing_data

open xi_time_part9h_escort_sector_freezing_data

private lemma xi_time_part9h_escort_sector_freezing_denominator_pos
    (D : xi_time_part9h_escort_sector_freezing_data) (m q : ℕ) :
    0 < D.xi_time_part9h_escort_sector_freezing_denominator m q := by
  have hterm_nonneg :
      ∀ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
        0 ≤ D.xi_time_part9h_escort_sector_freezing_weight m x ^ q := by
    intro x
    exact pow_nonneg (D.xi_time_part9h_escort_sector_freezing_weight_nonneg m x) q
  have hsingle :
      D.xi_time_part9h_escort_sector_freezing_maxWeight m ^ q ≤
        D.xi_time_part9h_escort_sector_freezing_denominator m q := by
    rw [xi_time_part9h_escort_sector_freezing_denominator,
      ← D.xi_time_part9h_escort_sector_freezing_maxIndex_spec m]
    exact Finset.single_le_sum (fun x _ => hterm_nonneg x) (Finset.mem_univ _)
  exact lt_of_lt_of_le (pow_pos (D.xi_time_part9h_escort_sector_freezing_max_pos m) q) hsingle

private lemma xi_time_part9h_escort_sector_freezing_bad_nonneg
    (D : xi_time_part9h_escort_sector_freezing_data) (m q : ℕ) :
    0 ≤ D.xi_time_part9h_escort_sector_freezing_sectorBadMass m q := by
  unfold xi_time_part9h_escort_sector_freezing_sectorBadMass
  refine div_nonneg ?_
    (le_of_lt (xi_time_part9h_escort_sector_freezing_denominator_pos D m q))
  refine Finset.sum_nonneg ?_
  intro x hx
  by_cases hbad : D.xi_time_part9h_escort_sector_freezing_sector m x = false
  · simp [hbad, pow_nonneg (D.xi_time_part9h_escort_sector_freezing_weight_nonneg m x) q]
  · simp [hbad]

/-- Paper label: `thm:xi-time-part9h-escort-sector-freezing`. -/
theorem paper_xi_time_part9h_escort_sector_freezing
    (D : xi_time_part9h_escort_sector_freezing_data) :
    xi_time_part9h_escort_sector_freezing_claim D := by
  have hpoint :
      ∀ m q,
        D.xi_time_part9h_escort_sector_freezing_sectorBadMass m q ≤
            D.xi_time_part9h_escort_sector_freezing_outsideMaxMass m q ∧
          D.xi_time_part9h_escort_sector_freezing_outsideMaxMass m q ≤
            D.xi_time_part9h_escort_sector_freezing_explicitBound m q := by
    intro m q
    have hden_pos := xi_time_part9h_escort_sector_freezing_denominator_pos D m q
    have hbad_outside_num :
        (∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
            if D.xi_time_part9h_escort_sector_freezing_sector m x = false then
              D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
            else
              0) ≤
          ∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
            if D.xi_time_part9h_escort_sector_freezing_weight m x ≠
                D.xi_time_part9h_escort_sector_freezing_maxWeight m then
              D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
            else
              0 := by
      refine Finset.sum_le_sum ?_
      intro x hx
      by_cases hbad : D.xi_time_part9h_escort_sector_freezing_sector m x = false
      · have hnotmax :
            D.xi_time_part9h_escort_sector_freezing_weight m x ≠
              D.xi_time_part9h_escort_sector_freezing_maxWeight m := by
          intro hmax
          have := D.xi_time_part9h_escort_sector_freezing_max_sector m x hmax
          simp [hbad] at this
        simp [hbad, hnotmax]
      · by_cases hxmax :
            D.xi_time_part9h_escort_sector_freezing_weight m x ≠
              D.xi_time_part9h_escort_sector_freezing_maxWeight m
        · simp [hbad, hxmax,
            pow_nonneg (D.xi_time_part9h_escort_sector_freezing_weight_nonneg m x) q]
        · simp [hbad, hxmax]
    have hfirst :
        D.xi_time_part9h_escort_sector_freezing_sectorBadMass m q ≤
          D.xi_time_part9h_escort_sector_freezing_outsideMaxMass m q := by
      unfold xi_time_part9h_escort_sector_freezing_sectorBadMass
        xi_time_part9h_escort_sector_freezing_outsideMaxMass
      exact div_le_div_of_nonneg_right hbad_outside_num (le_of_lt hden_pos)
    have houtside_num :
        (∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
            if D.xi_time_part9h_escort_sector_freezing_weight m x ≠
                D.xi_time_part9h_escort_sector_freezing_maxWeight m then
              D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
            else
              0) ≤
          (D.xi_time_part9h_escort_sector_freezing_card m : ℝ) *
            D.xi_time_part9h_escort_sector_freezing_secondWeight m ^ q := by
      calc
        (∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
            if D.xi_time_part9h_escort_sector_freezing_weight m x ≠
                D.xi_time_part9h_escort_sector_freezing_maxWeight m then
              D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
            else
              0)
            ≤ ∑ _x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
                D.xi_time_part9h_escort_sector_freezing_secondWeight m ^ q := by
              refine Finset.sum_le_sum ?_
              intro x hx
              by_cases hxmax :
                  D.xi_time_part9h_escort_sector_freezing_weight m x ≠
                    D.xi_time_part9h_escort_sector_freezing_maxWeight m
              · have hle :=
                  D.xi_time_part9h_escort_sector_freezing_second_bounds_complement m x hxmax
                have hpow :
                    D.xi_time_part9h_escort_sector_freezing_weight m x ^ q ≤
                      D.xi_time_part9h_escort_sector_freezing_secondWeight m ^ q :=
                  pow_le_pow_left₀
                    (D.xi_time_part9h_escort_sector_freezing_weight_nonneg m x) hle q
                simpa [hxmax] using hpow
              · simp [hxmax, pow_nonneg
                  (D.xi_time_part9h_escort_sector_freezing_second_nonneg m) q]
        _ = (D.xi_time_part9h_escort_sector_freezing_card m : ℝ) *
              D.xi_time_part9h_escort_sector_freezing_secondWeight m ^ q := by
              simp
    have hden_lower :
        D.xi_time_part9h_escort_sector_freezing_maxWeight m ^ q ≤
          D.xi_time_part9h_escort_sector_freezing_denominator m q := by
      rw [xi_time_part9h_escort_sector_freezing_denominator,
        ← D.xi_time_part9h_escort_sector_freezing_maxIndex_spec m]
      exact Finset.single_le_sum
        (fun x _ => pow_nonneg (D.xi_time_part9h_escort_sector_freezing_weight_nonneg m x) q)
        (Finset.mem_univ _)
    have hnum_nonneg :
        0 ≤
          ∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
            if D.xi_time_part9h_escort_sector_freezing_weight m x ≠
                D.xi_time_part9h_escort_sector_freezing_maxWeight m then
              D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
            else
              0 := by
      refine Finset.sum_nonneg ?_
      intro x hx
      by_cases hxmax :
          D.xi_time_part9h_escort_sector_freezing_weight m x ≠
            D.xi_time_part9h_escort_sector_freezing_maxWeight m
      · simp [hxmax, pow_nonneg (D.xi_time_part9h_escort_sector_freezing_weight_nonneg m x) q]
      · simp [hxmax]
    have hmaxpow_pos :
        0 < D.xi_time_part9h_escort_sector_freezing_maxWeight m ^ q :=
      pow_pos (D.xi_time_part9h_escort_sector_freezing_max_pos m) q
    have hsecond :
        D.xi_time_part9h_escort_sector_freezing_outsideMaxMass m q ≤
          D.xi_time_part9h_escort_sector_freezing_explicitBound m q := by
      unfold xi_time_part9h_escort_sector_freezing_outsideMaxMass
        xi_time_part9h_escort_sector_freezing_explicitBound
      calc
        (∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
            if D.xi_time_part9h_escort_sector_freezing_weight m x ≠
                D.xi_time_part9h_escort_sector_freezing_maxWeight m then
              D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
            else
              0) / D.xi_time_part9h_escort_sector_freezing_denominator m q
            ≤
          (∑ x : Fin (D.xi_time_part9h_escort_sector_freezing_card m),
            if D.xi_time_part9h_escort_sector_freezing_weight m x ≠
                D.xi_time_part9h_escort_sector_freezing_maxWeight m then
              D.xi_time_part9h_escort_sector_freezing_weight m x ^ q
            else
              0) /
            D.xi_time_part9h_escort_sector_freezing_maxWeight m ^ q := by
              exact div_le_div_of_nonneg_left hnum_nonneg hmaxpow_pos hden_lower
        _ ≤
          ((D.xi_time_part9h_escort_sector_freezing_card m : ℝ) *
              D.xi_time_part9h_escort_sector_freezing_secondWeight m ^ q) /
            D.xi_time_part9h_escort_sector_freezing_maxWeight m ^ q := by
              exact div_le_div_of_nonneg_right houtside_num
                (le_of_lt (pow_pos (D.xi_time_part9h_escort_sector_freezing_max_pos m) q))
    exact ⟨hfirst, hsecond⟩
  refine ⟨hpoint, ?_⟩
  intro qseq hqseq
  have hbad_tendsto :
      Tendsto
        (fun m : ℕ => D.xi_time_part9h_escort_sector_freezing_sectorBadMass m (qseq m))
        atTop (𝓝 0) := by
    refine squeeze_zero
      (fun m => xi_time_part9h_escort_sector_freezing_bad_nonneg D m (qseq m)) ?_
      (D.xi_time_part9h_escort_sector_freezing_asymptotic_bound qseq hqseq)
    intro m
    exact (hpoint m (qseq m)).1.trans ((hpoint m (qseq m)).2)
  simpa using (tendsto_const_nhds.sub hbad_tendsto)

end

end Omega.Zeta
