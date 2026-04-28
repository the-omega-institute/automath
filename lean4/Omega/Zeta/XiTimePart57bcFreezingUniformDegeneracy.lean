import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Total variation distance for finite real weights. -/
noncomputable def xi_time_part57bc_freezing_uniform_degeneracy_tv
    {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : α, |p x - q x|

/-- The normalized escort law attached to a finite weight function. -/
noncomputable def xi_time_part57bc_freezing_uniform_degeneracy_normalized
    {α : Type*} [Fintype α] (w : α → ℝ) (x : α) : ℝ :=
  w x / ∑ y : α, w y

/-- The uniform law on the frozen maximal layer. -/
noncomputable def xi_time_part57bc_freezing_uniform_degeneracy_uniformOn
    {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) (x : α) : ℝ :=
  if x ∈ A then ((A.card : ℝ)⁻¹) else 0

/-- Concrete finite two-layer freezing statement: the partition sum splits into the frozen layer
and its complement, a geometric remainder bound transfers to the normalized defect, and the total
variation distance from the frozen uniform law is exactly the outside mass. -/
def xi_time_part57bc_freezing_uniform_degeneracy_statement : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) (w : α → ℝ) (eps : ℝ),
    0 < A.card →
      (∀ x, 0 ≤ w x) →
      (∀ x, x ∈ A → w x = (∑ y ∈ A, w y) / (A.card : ℝ)) →
      0 ≤ eps →
      (∑ x ∈ Aᶜ, w x) ≤ eps * (∑ x ∈ A, w x) →
        let lead : ℝ := ∑ x ∈ A, w x
        let remainder : ℝ := ∑ x ∈ Aᶜ, w x
        let total : ℝ := ∑ x : α, w x
        total = lead + remainder ∧
          total ≤ (1 + eps) * lead ∧
          (0 < total →
            xi_time_part57bc_freezing_uniform_degeneracy_tv
                (xi_time_part57bc_freezing_uniform_degeneracy_normalized w)
                (xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A) =
              remainder / total)

/-- Paper label: `thm:xi-time-part57bc-freezing-uniform-degeneracy`. -/
theorem paper_xi_time_part57bc_freezing_uniform_degeneracy :
    xi_time_part57bc_freezing_uniform_degeneracy_statement := by
  classical
  intro α _ _ A w eps hAcard_pos hw_nonneg hw_frozen heps hrem
  let lead : ℝ := ∑ x ∈ A, w x
  let remainder : ℝ := ∑ x ∈ Aᶜ, w x
  let total : ℝ := ∑ x : α, w x
  have hrem' : remainder ≤ eps * lead := by
    simpa [lead, remainder] using hrem
  have htotal_split : total = lead + remainder := by
    have hsum :
        remainder + lead = total := by
      simpa [total, lead, remainder, Finset.compl_eq_univ_sdiff] using
        (Finset.sum_sdiff (Finset.subset_univ A) (f := w))
    linarith
  have htotal_bound : total ≤ (1 + eps) * lead := by
    calc
      total = lead + remainder := htotal_split
      _ ≤ lead + eps * lead := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hrem' lead
      _ = (1 + eps) * lead := by ring
  refine ⟨htotal_split, htotal_bound, ?_⟩
  intro htotal_pos
  have hcard_ne : (A.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hAcard_pos)
  have htotal_ne : total ≠ 0 := ne_of_gt htotal_pos
  have hremainder_nonneg : 0 ≤ remainder := by
    dsimp [remainder]
    exact Finset.sum_nonneg fun x _ => hw_nonneg x
  have hlead_le_total : lead ≤ total := by
    rw [htotal_split]
    exact le_add_of_nonneg_right hremainder_nonneg
  have hmass_le_one : lead / total ≤ 1 := by
    rw [div_le_one htotal_pos]
    exact hlead_le_total
  have hinside_abs :
      ∀ x ∈ A,
        |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x| =
          (1 - lead / total) / (A.card : ℝ) := by
    intro x hx
    have hwx : w x = lead / (A.card : ℝ) := by
      simpa [lead] using hw_frozen x hx
    have hnonneg : 0 ≤ (1 - lead / total) / (A.card : ℝ) := by
      exact div_nonneg (sub_nonneg.mpr hmass_le_one) (by exact_mod_cast le_of_lt hAcard_pos)
    rw [xi_time_part57bc_freezing_uniform_degeneracy_normalized,
      xi_time_part57bc_freezing_uniform_degeneracy_uniformOn, if_pos hx, hwx]
    have hcalc :
        lead / (A.card : ℝ) / total - (A.card : ℝ)⁻¹ =
          -((1 - lead / total) / (A.card : ℝ)) := by
      field_simp [hcard_ne, htotal_ne]
      ring
    rw [hcalc, abs_neg, abs_of_nonneg hnonneg]
  have houtside_abs :
      ∀ x ∈ Aᶜ,
        |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x| =
          w x / total := by
    intro x hx
    have hxA : x ∉ A := by simpa using hx
    rw [xi_time_part57bc_freezing_uniform_degeneracy_normalized,
      xi_time_part57bc_freezing_uniform_degeneracy_uniformOn, if_neg hxA, sub_zero]
    exact abs_of_nonneg (div_nonneg (hw_nonneg x) (le_of_lt htotal_pos))
  have hsum_split :
      (∑ x : α,
          |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|) =
        (∑ x ∈ A,
          |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|) +
        ∑ x ∈ Aᶜ,
          |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x| := by
    have hsum :
        (∑ x ∈ Aᶜ,
            |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
              xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|) +
          (∑ x ∈ A,
            |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
              xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|) =
          ∑ x : α,
            |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
              xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x| := by
      simpa [Finset.compl_eq_univ_sdiff] using
        (Finset.sum_sdiff (Finset.subset_univ A)
          (f := fun x : α =>
            |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
              xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|))
    linarith
  have hsum_inside :
      (∑ x ∈ A,
          |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|) =
        1 - lead / total := by
    calc
      (∑ x ∈ A,
          |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|)
          = ∑ _x ∈ A, (1 - lead / total) / (A.card : ℝ) := by
            exact Finset.sum_congr rfl fun x hx => hinside_abs x hx
      _ = (A.card : ℝ) * ((1 - lead / total) / (A.card : ℝ)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = 1 - lead / total := by field_simp [hcard_ne]
  have hsum_outside :
      (∑ x ∈ Aᶜ,
          |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|) =
        remainder / total := by
    calc
      (∑ x ∈ Aᶜ,
          |xi_time_part57bc_freezing_uniform_degeneracy_normalized w x -
            xi_time_part57bc_freezing_uniform_degeneracy_uniformOn A x|)
          = ∑ x ∈ Aᶜ, w x / total := by
            exact Finset.sum_congr rfl fun x hx => houtside_abs x hx
      _ = remainder / total := by
            dsimp [remainder]
            rw [Finset.sum_div]
  have hdefect :
      1 - lead / total = remainder / total := by
    calc
      1 - lead / total = (total - lead) / total := by
        field_simp [htotal_ne]
      _ = remainder / total := by
        rw [htotal_split]
        ring
  rw [xi_time_part57bc_freezing_uniform_degeneracy_tv, hsum_split, hsum_inside, hsum_outside,
    hdefect]
  ring

end Omega.Zeta
