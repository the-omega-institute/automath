import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite-fiber data for the capacity-curve inversion statement. -/
structure xi_time_part62df_capacity_curve_complete_inversion_data where
  xi_time_part62df_capacity_curve_complete_inversion_fiber : Type
  xi_time_part62df_capacity_curve_complete_inversion_fintype :
    Fintype xi_time_part62df_capacity_curve_complete_inversion_fiber
  xi_time_part62df_capacity_curve_complete_inversion_depth :
    xi_time_part62df_capacity_curve_complete_inversion_fiber → ℕ

/-- Tail count `#{x : n ≤ d x}`. -/
def xi_time_part62df_capacity_curve_complete_inversion_tail
    (D : xi_time_part62df_capacity_curve_complete_inversion_data) (n : ℕ) : ℕ := by
  letI := D.xi_time_part62df_capacity_curve_complete_inversion_fintype
  exact
    (Finset.univ.filter fun x :
      D.xi_time_part62df_capacity_curve_complete_inversion_fiber =>
        n ≤ D.xi_time_part62df_capacity_curve_complete_inversion_depth x).card

/-- Histogram count `#{x : d x = n}`. -/
def xi_time_part62df_capacity_curve_complete_inversion_hist
    (D : xi_time_part62df_capacity_curve_complete_inversion_data) (n : ℕ) : ℕ := by
  letI := D.xi_time_part62df_capacity_curve_complete_inversion_fintype
  exact
    (Finset.univ.filter fun x :
      D.xi_time_part62df_capacity_curve_complete_inversion_fiber =>
        D.xi_time_part62df_capacity_curve_complete_inversion_depth x = n).card

/-- Integer samples of the truncated capacity curve `sum_x min (d x) T`. -/
def xi_time_part62df_capacity_curve_complete_inversion_capacity
    (D : xi_time_part62df_capacity_curve_complete_inversion_data) (T : ℕ) : ℕ := by
  letI := D.xi_time_part62df_capacity_curve_complete_inversion_fintype
  exact
    ∑ x : D.xi_time_part62df_capacity_curve_complete_inversion_fiber,
      Nat.min (D.xi_time_part62df_capacity_curve_complete_inversion_depth x) T

/-- The inversion conclusion: first differences give tails, second differences give exact
multiplicities, and every finite symmetric functional groups by the recovered histogram. -/
def xi_time_part62df_capacity_curve_complete_inversion_conclusion
    (D : xi_time_part62df_capacity_curve_complete_inversion_data) : Prop :=
  letI := D.xi_time_part62df_capacity_curve_complete_inversion_fintype
  (∀ n : ℕ,
      xi_time_part62df_capacity_curve_complete_inversion_hist D n =
        xi_time_part62df_capacity_curve_complete_inversion_tail D n -
          xi_time_part62df_capacity_curve_complete_inversion_tail D (n + 1)) ∧
    (∀ n : ℕ, 1 ≤ n →
      xi_time_part62df_capacity_curve_complete_inversion_tail D n =
        xi_time_part62df_capacity_curve_complete_inversion_capacity D n -
          xi_time_part62df_capacity_curve_complete_inversion_capacity D (n - 1)) ∧
    (∀ F : ℕ → ℕ,
      (∑ x : D.xi_time_part62df_capacity_curve_complete_inversion_fiber,
          F (D.xi_time_part62df_capacity_curve_complete_inversion_depth x)) =
        (∑ n ∈ Finset.univ.image
          D.xi_time_part62df_capacity_curve_complete_inversion_depth,
          xi_time_part62df_capacity_curve_complete_inversion_hist D n * F n))

lemma xi_time_part62df_capacity_curve_complete_inversion_min_step
    (d n : ℕ) (hn : 1 ≤ n) :
    (if n ≤ d then 1 else 0) + Nat.min d (n - 1) = Nat.min d n := by
  by_cases hnd : n ≤ d
  · rw [if_pos hnd]
    have hpred : n - 1 ≤ d := by omega
    simp [hnd, hpred]
    omega
  · have hdlt : d < n := lt_of_not_ge hnd
    have hdle : d ≤ n - 1 := by omega
    simp [hnd, Nat.le_of_lt hdlt, hdle]

lemma xi_time_part62df_capacity_curve_complete_inversion_tail_eq_capacity_sub
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter fun x : ι => n ≤ d x).card =
      (∑ x : ι, Nat.min (d x) n) - (∑ x : ι, Nat.min (d x) (n - 1)) := by
  classical
  have hsum :
      (Finset.univ.filter fun x : ι => n ≤ d x).card +
          (∑ x : ι, Nat.min (d x) (n - 1)) =
        ∑ x : ι, Nat.min (d x) n := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    exact xi_time_part62df_capacity_curve_complete_inversion_min_step (d x) n hn
  exact Nat.eq_sub_of_add_eq' (by simpa [add_comm] using hsum)

lemma xi_time_part62df_capacity_curve_complete_inversion_hist_step
    (d n : ℕ) :
    (if d = n then 1 else 0) + (if n + 1 ≤ d then 1 else 0) =
      if n ≤ d then 1 else 0 := by
  by_cases hdn : d = n
  · subst hdn
    simp
  · by_cases hnd : n ≤ d
    · have hsucc : n + 1 ≤ d := by omega
      simp [hdn, hnd, hsucc]
    · have hsucc : ¬ n + 1 ≤ d := by omega
      simp [hdn, hnd, hsucc]

lemma xi_time_part62df_capacity_curve_complete_inversion_hist_eq_tail_sub
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (n : ℕ) :
    (Finset.univ.filter fun x : ι => d x = n).card =
      (Finset.univ.filter fun x : ι => n ≤ d x).card -
        (Finset.univ.filter fun x : ι => n + 1 ≤ d x).card := by
  classical
  have hsum :
      (Finset.univ.filter fun x : ι => d x = n).card +
          (Finset.univ.filter fun x : ι => n + 1 ≤ d x).card =
        (Finset.univ.filter fun x : ι => n ≤ d x).card := by
    repeat rw [Finset.card_eq_sum_ones]
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _hx
    exact xi_time_part62df_capacity_curve_complete_inversion_hist_step (d x) n
  exact Nat.eq_sub_of_add_eq' (by simpa [add_comm] using hsum)

lemma xi_time_part62df_capacity_curve_complete_inversion_group_by_hist
    {ι : Type*} [Fintype ι] (d : ι → ℕ) (F : ℕ → ℕ) :
    (∑ x : ι, F (d x)) =
      (∑ n ∈ Finset.univ.image d,
        (Finset.univ.filter fun x : ι => d x = n).card * F n) := by
  classical
  have hmaps :
      ∀ x ∈ (Finset.univ : Finset ι), d x ∈ (Finset.univ.image d) := by
    intro x hx
    exact Finset.mem_image_of_mem d hx
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset ι))
      (t := Finset.univ.image d) (g := d) hmaps F
  symm
  calc
    (∑ n ∈ Finset.univ.image d,
        (Finset.univ.filter fun x : ι => d x = n).card * F n)
        = ∑ n ∈ Finset.univ.image d,
            ∑ x ∈ (Finset.univ.filter fun x : ι => d x = n), F n := by
          refine Finset.sum_congr rfl ?_
          intro n _hn
          simp
    _ = ∑ x ∈ (Finset.univ : Finset ι), F (d x) := by
          simpa using hfiber
    _ = ∑ x : ι, F (d x) := by
          simp

/-- Paper label: `thm:xi-time-part62df-capacity-curve-complete-inversion`. -/
theorem paper_xi_time_part62df_capacity_curve_complete_inversion
    (D : xi_time_part62df_capacity_curve_complete_inversion_data) :
    xi_time_part62df_capacity_curve_complete_inversion_conclusion D := by
  classical
  letI := D.xi_time_part62df_capacity_curve_complete_inversion_fintype
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [xi_time_part62df_capacity_curve_complete_inversion_hist,
      xi_time_part62df_capacity_curve_complete_inversion_tail] using
      xi_time_part62df_capacity_curve_complete_inversion_hist_eq_tail_sub
        D.xi_time_part62df_capacity_curve_complete_inversion_depth n
  · intro n hn
    simpa [xi_time_part62df_capacity_curve_complete_inversion_tail,
      xi_time_part62df_capacity_curve_complete_inversion_capacity] using
      xi_time_part62df_capacity_curve_complete_inversion_tail_eq_capacity_sub
        D.xi_time_part62df_capacity_curve_complete_inversion_depth n hn
  · intro F
    simpa [xi_time_part62df_capacity_curve_complete_inversion_hist] using
      xi_time_part62df_capacity_curve_complete_inversion_group_by_hist
        D.xi_time_part62df_capacity_curve_complete_inversion_depth F

end Omega.Zeta
