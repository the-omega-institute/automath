import Mathlib
import Omega.Folding.FoldBinGaugeVolumeStieltjesSum

namespace Omega.Folding

open scoped BigOperators

/-- Paper label: `prop:foldbin-tailcount-bound-from-s2`. Splitting the finite type into the
`d(a) ≥ k` and `d(a) < k` fibers yields the stated universal tail bound from the quadratic
collision moment. -/
theorem paper_foldbin_tailcount_bound_from_s2 {α : Type*} [Fintype α] (d : α → ℕ) (k : ℕ)
    (hk : 2 ≤ k) (hpos : ∀ a, 1 ≤ d a) :
    foldBinTailCount d (k - 1) ≤ ((∑ a, d a ^ 2) - Fintype.card α) / (k ^ 2 - 1) := by
  classical
  let paper_foldbin_tailcount_bound_from_s2_heavy : Finset α :=
    Finset.univ.filter (fun a => k ≤ d a)
  let paper_foldbin_tailcount_bound_from_s2_light : Finset α :=
    Finset.univ.filter (fun a => ¬ k ≤ d a)
  have hk_sq : 4 ≤ k ^ 2 := by
    simpa using (Nat.pow_le_pow_left hk 2)
  have hk_pos : 0 < k ^ 2 - 1 := by
    exact Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 4) hk_sq)
  have hk_one : 1 ≤ k := by
    omega
  have htail :
      foldBinTailCount d (k - 1) = paper_foldbin_tailcount_bound_from_s2_heavy.card := by
    rw [foldBinTailCount, Nat.sub_add_cancel hk_one]
    have hcard :
        Fintype.card {a // k ≤ d a} = paper_foldbin_tailcount_bound_from_s2_heavy.card := by
      simpa [paper_foldbin_tailcount_bound_from_s2_heavy] using
        (Fintype.card_of_subtype (p := fun a : α => k ≤ d a)
          paper_foldbin_tailcount_bound_from_s2_heavy (by
            intro a
            simp [paper_foldbin_tailcount_bound_from_s2_heavy]))
    simpa [paper_foldbin_tailcount_bound_from_s2_heavy] using hcard
  have hheavy :
      paper_foldbin_tailcount_bound_from_s2_heavy.sum (fun _ => k ^ 2) ≤
        paper_foldbin_tailcount_bound_from_s2_heavy.sum (fun a => d a ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro a ha
    have hka : k ≤ d a := by
      simp [paper_foldbin_tailcount_bound_from_s2_heavy] at ha
      exact ha
    exact Nat.pow_le_pow_left hka 2
  have hlight :
      paper_foldbin_tailcount_bound_from_s2_light.sum (fun _ => 1) ≤
        paper_foldbin_tailcount_bound_from_s2_light.sum (fun a => d a ^ 2) := by
    refine Finset.sum_le_sum ?_
    intro a ha
    have hda : 1 ≤ d a := hpos a
    simpa using Nat.pow_le_pow_left hda 2
  have hsplit_sum :
      (Finset.univ : Finset α).sum (fun a => d a ^ 2) =
        paper_foldbin_tailcount_bound_from_s2_heavy.sum (fun a => d a ^ 2) +
          paper_foldbin_tailcount_bound_from_s2_light.sum (fun a => d a ^ 2) := by
    simpa [paper_foldbin_tailcount_bound_from_s2_heavy, paper_foldbin_tailcount_bound_from_s2_light]
      using
        (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset α))
          (p := fun a => k ≤ d a) (f := fun a => d a ^ 2)).symm
  have hsplit_card :
      paper_foldbin_tailcount_bound_from_s2_heavy.card +
          paper_foldbin_tailcount_bound_from_s2_light.card =
        Fintype.card α := by
    simpa [paper_foldbin_tailcount_bound_from_s2_heavy, paper_foldbin_tailcount_bound_from_s2_light]
      using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
          (p := fun a => k ≤ d a))
  have hmain :
      Fintype.card α +
          paper_foldbin_tailcount_bound_from_s2_heavy.card * (k ^ 2 - 1) ≤
        ∑ a, d a ^ 2 := by
    have hsum :
        paper_foldbin_tailcount_bound_from_s2_heavy.card * k ^ 2 +
            paper_foldbin_tailcount_bound_from_s2_light.card ≤
          paper_foldbin_tailcount_bound_from_s2_heavy.sum (fun a => d a ^ 2) +
            paper_foldbin_tailcount_bound_from_s2_light.sum (fun a => d a ^ 2) := by
      refine add_le_add ?_ ?_
      · simpa [paper_foldbin_tailcount_bound_from_s2_heavy, Finset.sum_const, nsmul_eq_mul] using
          hheavy
      · simpa [paper_foldbin_tailcount_bound_from_s2_light, Finset.sum_const] using hlight
    have hrewrite :
        Fintype.card α + paper_foldbin_tailcount_bound_from_s2_heavy.card * (k ^ 2 - 1) =
          paper_foldbin_tailcount_bound_from_s2_heavy.card * k ^ 2 +
            paper_foldbin_tailcount_bound_from_s2_light.card := by
      calc
        Fintype.card α + paper_foldbin_tailcount_bound_from_s2_heavy.card * (k ^ 2 - 1) =
            paper_foldbin_tailcount_bound_from_s2_heavy.card +
              paper_foldbin_tailcount_bound_from_s2_light.card +
                paper_foldbin_tailcount_bound_from_s2_heavy.card * (k ^ 2 - 1) := by
                  rw [hsplit_card.symm]
        _ =
            paper_foldbin_tailcount_bound_from_s2_heavy.card * k ^ 2 +
              paper_foldbin_tailcount_bound_from_s2_light.card := by
                calc
                  paper_foldbin_tailcount_bound_from_s2_heavy.card +
                      paper_foldbin_tailcount_bound_from_s2_light.card +
                        paper_foldbin_tailcount_bound_from_s2_heavy.card * (k ^ 2 - 1) =
                      paper_foldbin_tailcount_bound_from_s2_light.card +
                        (paper_foldbin_tailcount_bound_from_s2_heavy.card * (k ^ 2 - 1) +
                          paper_foldbin_tailcount_bound_from_s2_heavy.card) := by
                            ac_rfl
                  _ =
                      paper_foldbin_tailcount_bound_from_s2_light.card +
                        paper_foldbin_tailcount_bound_from_s2_heavy.card * ((k ^ 2 - 1) + 1) := by
                          simp [Nat.mul_add, add_assoc, add_comm]
                  _ =
                      paper_foldbin_tailcount_bound_from_s2_light.card +
                        paper_foldbin_tailcount_bound_from_s2_heavy.card * (k ^ 2) := by
                          rw [Nat.sub_add_cancel (by omega : 1 ≤ k ^ 2)]
                  _ =
                      paper_foldbin_tailcount_bound_from_s2_heavy.card * k ^ 2 +
                        paper_foldbin_tailcount_bound_from_s2_light.card := by
                          ac_rfl
    rw [hsplit_sum, hrewrite]
    exact hsum
  have hnum :
      foldBinTailCount d (k - 1) * (k ^ 2 - 1) ≤ (∑ a, d a ^ 2) - Fintype.card α := by
    rw [htail]
    omega
  exact (Nat.le_div_iff_mul_le hk_pos).2 hnum

end Omega.Folding
