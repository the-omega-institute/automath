import Mathlib.Tactic
import Mathlib.Algebra.Field.GeomSum
import Omega.SPG.DyadicFluxZetaMinkowskiPole

namespace Omega.SPG

open Finset

/-- Rank-one linear representation `N_m = u * M^m * v`.
    This is the scalar avatar of the finite-state representation used in the paper-facing zeta
    package. `prop:spg-regular-language-stokes-dyadic-zeta-rationality` -/
noncomputable def regularLanguageCount (u M v : ℝ) (m : ℕ) : ℝ :=
  u * M ^ m * v

/-- Finite Stokes--dyadic flux zeta sum for the scalar linear representation.
    `prop:spg-regular-language-stokes-dyadic-zeta-rationality` -/
noncomputable def stokesDyadicZetaPartial (u M v z : ℝ) (k : ℕ) : ℝ :=
  ∑ m in Finset.range k, regularLanguageCount u M v m * z ^ m

/-- The scalar linear representation packages the dyadic zeta sum as a geometric series, hence as
    a rational function of the dyadic weight `z`. The `z = 1/2` specialization recovers the
    nearby dyadic-flux seed `15/8`.
    prop:spg-regular-language-stokes-dyadic-zeta-rationality -/
theorem paper_spg_regular_language_stokes_dyadic_zeta_rationality
    (u M v z : ℝ) (k : ℕ) :
    stokesDyadicZetaPartial u M v z k = (u * v) * ∑ m in Finset.range k, (M * z) ^ m ∧
      (M * z ≠ 1 →
        stokesDyadicZetaPartial u M v z k =
          (u * v) * (((M * z) ^ k - 1) / (M * z - 1))) ∧
      stokesDyadicZetaPartial 1 1 1 (1 / 2) 4 = 15 / 8 := by
  have hgeom :
      stokesDyadicZetaPartial u M v z k = (u * v) * ∑ m in Finset.range k, (M * z) ^ m := by
    unfold stokesDyadicZetaPartial regularLanguageCount
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [mul_pow]
    ring
  refine ⟨hgeom, ?_, ?_⟩
  · intro hz
    rw [hgeom, geom_sum_eq hz]
  · have hseed :
        stokesDyadicZetaPartial 1 1 1 (1 / 2) 4 =
          ((1 : ℝ) + 1 / 2 + 1 / 4 + 1 / 8) := by
      norm_num [stokesDyadicZetaPartial, regularLanguageCount]
    rw [hseed]
    norm_num

end Omega.SPG
