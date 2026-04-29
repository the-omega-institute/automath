import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Zeta

lemma xi_time_part74_smith_loss_fixed_total_valuation_extremal_min_add_le
    (k a b : ℕ) : min k (a + b) ≤ min k a + min k b := by
  by_cases ha : k ≤ a
  · have hleft : min k (a + b) ≤ k := Nat.min_le_left k (a + b)
    rw [min_eq_left ha]
    exact le_trans hleft (Nat.le_add_right k (min k b))
  · have ha' : a ≤ k := Nat.le_of_not_ge ha
    by_cases hb : k ≤ b
    · have hleft : min k (a + b) ≤ k := Nat.min_le_left k (a + b)
      rw [min_eq_right ha', min_eq_left hb]
      omega
    · have hb' : b ≤ k := Nat.le_of_not_ge hb
      by_cases hab : a + b ≤ k
      · rw [min_eq_right hab, min_eq_right ha', min_eq_right hb']
      · have hk : k ≤ a + b := Nat.le_of_not_ge hab
        rw [min_eq_left hk, min_eq_right ha', min_eq_right hb']
        omega

lemma xi_time_part74_smith_loss_fixed_total_valuation_extremal_min_sum_le_sum_min
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (k : ℕ) (e : ι → ℕ) :
    min k (∑ i ∈ s, e i) ≤ (∑ i ∈ s, min k (e i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans
      (xi_time_part74_smith_loss_fixed_total_valuation_extremal_min_add_le
        k (e a) (∑ i ∈ s, e i))
      (Nat.add_le_add_left ih (min k (e a)))

lemma xi_time_part74_smith_loss_fixed_total_valuation_extremal_balanced_sum
    (m r a b : ℕ) (hr : r ≤ m) :
    (∑ i : Fin m, if (i : ℕ) < r then a else b) = r * a + (m - r) * b := by
  rw [← Finset.sum_range (fun x => if x < r then a else b)]
  conv_lhs => rw [← Nat.add_sub_of_le hr]
  rw [Finset.sum_range_add]
  have hnot : ∀ x : ℕ, ¬r + x < r := by
    intro x
    omega
  have hfirst : (∑ x ∈ Finset.range r, if x < r then a else b) = r * a := by
    calc
      (∑ x ∈ Finset.range r, if x < r then a else b) = ∑ _x ∈ Finset.range r, a := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simp [Finset.mem_range.mp hx]
      _ = r * a := by simp
  have hsecond :
      (∑ x ∈ Finset.range (m - r), if r + x < r then a else b) = (m - r) * b := by
    calc
      (∑ x ∈ Finset.range (m - r), if r + x < r then a else b) =
          ∑ _x ∈ Finset.range (m - r), b := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        simp [hnot x]
      _ = (m - r) * b := by simp
  rw [hfirst, hsecond]

lemma xi_time_part74_smith_loss_fixed_total_valuation_extremal_balanced_total
    (m q r : ℕ) (hr : r ≤ m) :
    (m - r) * q + r * (q + 1) = m * q + r := by
  calc
    (m - r) * q + r * (q + 1) = (r + (m - r)) * q + r := by
      rw [Nat.mul_succ, Nat.add_mul]
      ac_rfl
    _ = m * q + r := by rw [Nat.add_sub_of_le hr]

lemma xi_time_part74_smith_loss_fixed_total_valuation_extremal_balanced_total'
    (m q r : ℕ) (hr : r ≤ m) :
    r * (q + 1) + (m - r) * q = m * q + r := by
  rw [add_comm]
  exact xi_time_part74_smith_loss_fixed_total_valuation_extremal_balanced_total m q r hr

/-- Paper label: `thm:xi-time-part74-smith-loss-fixed-total-valuation-extremal`. -/
theorem paper_xi_time_part74_smith_loss_fixed_total_valuation_extremal
    (m k E q r : ℕ) (hm : 0 < m) (hE : E = m * q + r) (hr : r < m) :
    (∀ e : Fin m → ℕ, (∑ i, e i) = E →
      min k E ≤ ∑ i, min k (e i) ∧
        ∑ i, min k (e i) ≤ (m - r) * min k q + r * min k (q + 1)) ∧
      (∃ eMin : Fin m → ℕ, (∑ i, eMin i) = E ∧
        ∑ i, min k (eMin i) = min k E) ∧
      (∃ eMax : Fin m → ℕ, (∑ i, eMax i) = E ∧
        ∑ i, min k (eMax i) = (m - r) * min k q + r * min k (q + 1)) := by
  classical
  have hrle : r ≤ m := le_of_lt hr
  refine ⟨?_, ?_, ?_⟩
  · intro e hsum
    constructor
    · rw [← hsum]
      exact
        xi_time_part74_smith_loss_fixed_total_valuation_extremal_min_sum_le_sum_min
          (Finset.univ : Finset (Fin m)) k e
    · by_cases hq : q < k
      · have hminq : min k q = q := min_eq_right (Nat.le_of_lt hq)
        have hminq1 : min k (q + 1) = q + 1 := min_eq_right (Nat.succ_le_of_lt hq)
        have hright :
            (m - r) * min k q + r * min k (q + 1) = E := by
          rw [hminq, hminq1, hE]
          exact
            xi_time_part74_smith_loss_fixed_total_valuation_extremal_balanced_total
              m q r hrle
        rw [hright]
        exact le_trans (Finset.sum_le_sum fun i _ => Nat.min_le_right k (e i)) (le_of_eq hsum)
      · have hkq : k ≤ q := Nat.le_of_not_gt hq
        have hminq : min k q = k := min_eq_left hkq
        have hminq1 : min k (q + 1) = k := min_eq_left (by omega)
        have hright :
            (m - r) * min k q + r * min k (q + 1) = m * k := by
          rw [hminq, hminq1]
          calc
            (m - r) * k + r * k = ((m - r) + r) * k := by rw [Nat.add_mul]
            _ = m * k := by rw [Nat.sub_add_cancel hrle]
        rw [hright]
        calc
          ∑ i : Fin m, min k (e i) ≤ ∑ _i : Fin m, k :=
            Finset.sum_le_sum fun i _ => Nat.min_le_left k (e i)
          _ = m * k := by simp [Fintype.card_fin]
  · let i0 : Fin m := ⟨0, hm⟩
    refine ⟨fun i => if i = i0 then E else 0, ?_, ?_⟩
    · rw [Finset.sum_eq_single i0]
      · simp
      · intro b _hb hbi
        simp [hbi]
      · intro hi0
        exact False.elim (hi0 (Finset.mem_univ i0))
    · rw [Finset.sum_eq_single i0]
      · simp
      · intro b _hb hbi
        simp [hbi]
      · intro hi0
        exact False.elim (hi0 (Finset.mem_univ i0))
  · refine ⟨fun i : Fin m => if (i : ℕ) < r then q + 1 else q, ?_, ?_⟩
    · rw [xi_time_part74_smith_loss_fixed_total_valuation_extremal_balanced_sum m r (q + 1) q hrle]
      rw [hE]
      exact
        xi_time_part74_smith_loss_fixed_total_valuation_extremal_balanced_total'
          m q r hrle
    · have hbalanced :=
        xi_time_part74_smith_loss_fixed_total_valuation_extremal_balanced_sum
          m r (min k (q + 1)) (min k q) hrle
      calc
        ∑ i : Fin m, min k ((fun i : Fin m => if (i : ℕ) < r then q + 1 else q) i) =
            ∑ i : Fin m, if (i : ℕ) < r then min k (q + 1) else min k q := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hir : (i : ℕ) < r <;> simp [hir]
        _ = r * min k (q + 1) + (m - r) * min k q := hbalanced
        _ = (m - r) * min k q + r * min k (q + 1) := by ac_rfl

end Omega.Zeta
