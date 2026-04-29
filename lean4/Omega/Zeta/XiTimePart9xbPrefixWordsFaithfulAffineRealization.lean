import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

universe u

/-- Product of the affine slopes attached to a finite prefix word. -/
def xi_time_part9xb_prefix_words_faithful_affine_realization_wordSlope
    {Letter : Type u} (scale : Letter → ℝ) : List Letter → ℝ
  | [] => 1
  | a :: w =>
      scale a * xi_time_part9xb_prefix_words_faithful_affine_realization_wordSlope scale w

/-- Translation part of the affine map attached to a finite prefix word. -/
def xi_time_part9xb_prefix_words_faithful_affine_realization_wordOffset
    {Letter : Type u} (scale shift : Letter → ℝ) : List Letter → ℝ
  | [] => 0
  | a :: w =>
      scale a *
          xi_time_part9xb_prefix_words_faithful_affine_realization_wordOffset scale shift w +
        shift a

/-- Recursive action of a finite prefix word by affine maps, read from left to right. -/
def xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction
    {Letter : Type u} (scale shift : Letter → ℝ) : List Letter → ℝ → ℝ
  | [], x => x
  | a :: w, x =>
      scale a *
          xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction scale shift w x +
        shift a

/-- The affine signature of a finite prefix word. -/
def xi_time_part9xb_prefix_words_faithful_affine_realization_wordSignature
    {Letter : Type u} (scale shift : Letter → ℝ) (w : List Letter) : ℝ × ℝ :=
  (xi_time_part9xb_prefix_words_faithful_affine_realization_wordSlope scale w,
    xi_time_part9xb_prefix_words_faithful_affine_realization_wordOffset scale shift w)

/-- Concrete data for a faithful affine realization of finite prefix words.  The final
injectivity hypothesis is the audited affine-submonoid separation of word signatures. -/
structure xi_time_part9xb_prefix_words_faithful_affine_realization_data where
  Letter : Type u
  scale : Letter → ℝ
  shift : Letter → ℝ
  scale_ne_zero : ∀ a, scale a ≠ 0
  wordSignature_injective :
    Function.Injective
      (xi_time_part9xb_prefix_words_faithful_affine_realization_wordSignature scale shift)

namespace xi_time_part9xb_prefix_words_faithful_affine_realization_data

/-- The recursive prefix action has the advertised affine closed form. -/
def prefix_formula (D : xi_time_part9xb_prefix_words_faithful_affine_realization_data) : Prop :=
  ∀ (w : List D.Letter) (x : ℝ),
    xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction D.scale D.shift w x =
      xi_time_part9xb_prefix_words_faithful_affine_realization_wordSlope D.scale w * x +
        xi_time_part9xb_prefix_words_faithful_affine_realization_wordOffset D.scale D.shift w

/-- Concatenation of words is represented by composition of their affine actions. -/
def affine_monoid_hom
    (D : xi_time_part9xb_prefix_words_faithful_affine_realization_data) : Prop :=
  ∀ (u v : List D.Letter) (x : ℝ),
    xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction D.scale D.shift
        (u ++ v) x =
      xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction D.scale D.shift u
        (xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction D.scale D.shift
          v x)

/-- Distinct prefix words induce distinct affine maps. -/
def faithful (D : xi_time_part9xb_prefix_words_faithful_affine_realization_data) : Prop :=
  Function.Injective
    (fun w : List D.Letter =>
      xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction D.scale D.shift w)

end xi_time_part9xb_prefix_words_faithful_affine_realization_data

/-- Paper label: `thm:xi-time-part9xb-prefix-words-faithful-affine-realization`. -/
theorem paper_xi_time_part9xb_prefix_words_faithful_affine_realization
    (D : xi_time_part9xb_prefix_words_faithful_affine_realization_data) :
    D.prefix_formula ∧ D.affine_monoid_hom ∧ D.faithful := by
  classical
  have hprefix : D.prefix_formula := by
    intro w x
    induction w with
    | nil =>
        simp [xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction,
          xi_time_part9xb_prefix_words_faithful_affine_realization_wordSlope,
          xi_time_part9xb_prefix_words_faithful_affine_realization_wordOffset]
    | cons a w ih =>
        simp [xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction,
          xi_time_part9xb_prefix_words_faithful_affine_realization_wordSlope,
          xi_time_part9xb_prefix_words_faithful_affine_realization_wordOffset, ih,
          left_distrib, mul_assoc, add_assoc]
  have hhom : D.affine_monoid_hom := by
    intro u v x
    induction u with
    | nil =>
        simp [xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction]
    | cons a u ih =>
        simp [xi_time_part9xb_prefix_words_faithful_affine_realization_wordAction, ih]
  have hfaithful : D.faithful := by
    intro u v huv
    have h0 := congrFun huv 0
    have h1 := congrFun huv 1
    have hoffset :
        xi_time_part9xb_prefix_words_faithful_affine_realization_wordOffset D.scale D.shift u =
          xi_time_part9xb_prefix_words_faithful_affine_realization_wordOffset D.scale D.shift
            v := by
      simp only at h0
      rw [hprefix u 0, hprefix v 0] at h0
      simpa using h0
    have hslope :
        xi_time_part9xb_prefix_words_faithful_affine_realization_wordSlope D.scale u =
          xi_time_part9xb_prefix_words_faithful_affine_realization_wordSlope D.scale v := by
      simp only at h1
      rw [hprefix u 1, hprefix v 1] at h1
      nlinarith
    exact D.wordSignature_injective (Prod.ext hslope hoffset)
  exact ⟨hprefix, hhom, hfaithful⟩

end Omega.Zeta
