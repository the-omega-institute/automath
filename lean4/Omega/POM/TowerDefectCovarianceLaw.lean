import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

/-- The finite fiber `f⁻¹(b)` as a `Finset`. -/
def towerFiber (f : α → β) (b : β) : Finset α :=
  Finset.univ.filter fun a => f a = b

/-- Cardinality of a finite fiber. -/
def towerFiberCard (f : α → β) (b : β) : ℕ :=
  (towerFiber f b).card

/-- Uniform average over a finite fiber. -/
noncomputable def towerFiberAverage (f : α → β) (φ : α → ℚ) (b : β) : ℚ :=
  Finset.sum (towerFiber f b) φ / (towerFiberCard f b : ℚ)

/-- Weighted average over a finite fiber. -/
noncomputable def towerFiberWeightedAverage (f : α → β) (w φ : α → ℚ) (b : β) : ℚ :=
  Finset.sum (towerFiber f b) (fun a => w a * φ a) / Finset.sum (towerFiber f b) w

/-- Uniform covariance on a finite fiber. -/
noncomputable def towerFiberCovariance (f : α → β) (u v : α → ℚ) (b : β) : ℚ :=
  towerFiberAverage f (fun a => u a * v a) b - towerFiberAverage f u b * towerFiberAverage f v b

private lemma towerFiberAverage_sub_weightedAverage_eq_neg_cov_div_mean
    (f : α → β) (w v : α → ℚ) (b : β) (hb : 0 < towerFiberCard f b)
    (hw : 0 < Finset.sum (towerFiber f b) w) :
    towerFiberAverage f v b - towerFiberWeightedAverage f w v b =
      -towerFiberCovariance f w v b / towerFiberAverage f w b := by
  let s : Finset α := towerFiber f b
  let n : ℚ := towerFiberCard f b
  let wsum : ℚ := Finset.sum s w
  let vsum : ℚ := Finset.sum s v
  let cross : ℚ := Finset.sum s (fun a => w a * v a)
  have hn : n ≠ 0 := by
    dsimp [n, towerFiberCard]
    exact_mod_cast hb.ne'
  have hwsum : wsum ≠ 0 := by
    dsimp [wsum]
    exact_mod_cast hw.ne'
  have hmean : wsum / n ≠ 0 := div_ne_zero hwsum hn
  dsimp [towerFiberAverage, towerFiberWeightedAverage, towerFiberCovariance, s, n, wsum, vsum,
    cross]
  field_simp [hn, hwsum, hmean]
  ring

lemma towerFiberCard_pos_of_surjective (f : α → β) (hf : Function.Surjective f) (b : β) :
    0 < towerFiberCard f b := by
  rcases hf b with ⟨a, rfl⟩
  refine Finset.card_pos.mpr ?_
  exact ⟨a, by simp [towerFiber]⟩

private lemma sum_towerFiberCard_pos {γ : Type*} [Fintype γ] [DecidableEq γ]
    (g : γ → α) (hf : Function.Surjective g) (s : Finset α) (hs : 0 < s.card) :
    0 < Finset.sum s (fun a => towerFiberCard g a) := by
  rcases Finset.card_pos.mp hs with ⟨a, ha⟩
  have haPos : 0 < towerFiberCard g a := towerFiberCard_pos_of_surjective g hf a
  have hle :
      towerFiberCard g a ≤ Finset.sum s (fun a' => towerFiberCard g a') := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
  exact lt_of_lt_of_le haPos hle

section TowerLaw

variable {X Y Z : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

/-- The inner uniform fiber average `A_g ψ`. -/
noncomputable def towerInnerAverage (g : X → Y) (ψ : X → ℚ) : Y → ℚ :=
  fun y => towerFiberAverage g ψ y

/-- The size-biased outer average corresponding to the composite fibers of `h ∘ g`. -/
noncomputable def towerCompositeAverage (g : X → Y) (h : Y → Z) (ψ : X → ℚ) (z : Z) : ℚ :=
  towerFiberWeightedAverage h (fun y => (towerFiberCard g y : ℚ)) (towerInnerAverage g ψ) z

/-- The covariance term comparing the uniform outer average with the size-biased composite
average. -/
noncomputable def towerDefectCovariance (g : X → Y) (h : Y → Z) (ψ : X → ℚ) (z : Z) : ℚ :=
  towerFiberCovariance h (fun y => (towerFiberCard g y : ℚ)) (towerInnerAverage g ψ) z

/-- For a surjection `g`, the difference between the outer uniform average `A_h (A_g ψ)` and the
size-biased composite average `A_{h ∘ g} ψ` is exactly the normalized covariance of the fiber
degrees `d_g` with the inner averages `A_g ψ`.
    thm:pom-tower-defect-covariance-law -/
theorem paper_pom_tower_defect_covariance_law
    (g : X → Y) (h : Y → Z) (ψ : X → ℚ) (hg : Function.Surjective g)
    (z : Z) (hz : 0 < towerFiberCard h z) :
    towerFiberAverage h (towerInnerAverage g ψ) z - towerCompositeAverage g h ψ z =
      -towerDefectCovariance g h ψ z / towerFiberAverage h (fun y => (towerFiberCard g y : ℚ)) z := by
  have hd :
      0 < Finset.sum (towerFiber h z) (fun y => (towerFiberCard g y : ℚ)) := by
    have hnat :
        0 < Finset.sum (towerFiber h z) (fun y => towerFiberCard g y) :=
      sum_towerFiberCard_pos g hg (towerFiber h z) (by simpa [towerFiberCard] using hz)
    exact_mod_cast hnat
  simpa [towerCompositeAverage, towerDefectCovariance, towerInnerAverage] using
    towerFiberAverage_sub_weightedAverage_eq_neg_cov_div_mean
      (f := h) (w := fun y => (towerFiberCard g y : ℚ)) (v := towerInnerAverage g ψ) z
      (by simpa [towerFiberCard] using hz) hd

end TowerLaw

end Omega.POM
