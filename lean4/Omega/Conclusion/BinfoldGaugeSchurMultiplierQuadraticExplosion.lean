import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter

/-- The audited fiber indices at stage `m`. -/
abbrev conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_fiber
    (fiberCount : ℕ → ℕ) (m : ℕ) :=
  Fin (fiberCount m)

/-- The local threshold at which every symmetric-group factor contributes one Schur multiplier
and one abelianized `ZMod 2` tensor coordinate. -/
def conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_stableFiberSize : ℕ := 7

/-- The product-formula rank once all fibers are in the stable range. -/
def conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_productRank
    (fiberCount : ℕ) : ℕ :=
  fiberCount + Nat.choose fiberCount 2

lemma conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_productRank_eq
    (fiberCount : ℕ) :
    conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_productRank fiberCount =
      fiberCount * (fiberCount + 1) / 2 := by
  unfold conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_productRank
  calc
    fiberCount + Nat.choose fiberCount 2 =
        Nat.choose fiberCount 1 + Nat.choose fiberCount 2 := by
          rw [Nat.choose_one_right]
    _ = Nat.choose (fiberCount + 1) 2 := by
          simpa [Nat.add_comm] using (Nat.choose_succ_succ fiberCount 1).symm
    _ = (fiberCount + 1) * ((fiberCount + 1) - 1) / 2 := by
          rw [Nat.choose_two_right]
    _ = fiberCount * (fiberCount + 1) / 2 := by
          rw [Nat.add_sub_cancel, Nat.mul_comm]

/-- Eventual lower bound for the finite bin-fold fiber profile. -/
def conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_eventualLowerBound
    (fiberCount : ℕ → ℕ)
    (fiberSize :
      (m : ℕ) →
        conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_fiber fiberCount m → ℕ) :
    Prop :=
  ∀ᶠ m in atTop,
    ∀ w : conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_fiber fiberCount m,
      conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_stableFiberSize ≤
        fiberSize m w

/-- The finite-product Schur multiplier rank formula in the stable symmetric-group range. -/
def conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_productFormula
    (fiberCount schurMultiplierRank : ℕ → ℕ)
    (fiberSize :
      (m : ℕ) →
        conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_fiber fiberCount m → ℕ) :
    Prop :=
  ∀ᶠ m in atTop,
    (∀ w : conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_fiber fiberCount m,
      conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_stableFiberSize ≤
        fiberSize m w) →
      schurMultiplierRank m =
        conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_productRank
          (fiberCount m)

/-- Concrete rank form for
`thm:conclusion-binfold-gauge-schur-multiplier-quadratic-explosion`.

Once every bin-fold fiber is eventually in the stable `d_m(w) >= 7` range, the product formula
gives `n_m` local Schur multiplier coordinates and `choose n_m 2` tensor coordinates, hence the
eventual quadratic exponent `n_m(n_m+1)/2`. The paper-facing declaration is already present in the
rebased chapter under the same Lean name, so this target file records the concrete non-shell
finite-stage proof without redeclaring that global symbol. -/
theorem conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_eventual_rank
    (fiberCount schurMultiplierRank : ℕ → ℕ)
    (fiberSize :
      (m : ℕ) →
        conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_fiber fiberCount m → ℕ)
    (hLower :
      conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_eventualLowerBound
        fiberCount fiberSize)
    (hProduct :
      conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_productFormula
        fiberCount schurMultiplierRank fiberSize) :
    ∃ m0 : ℕ, ∀ m ≥ m0,
      schurMultiplierRank m = fiberCount m * (fiberCount m + 1) / 2 := by
  have hevent :
      ∀ᶠ m in atTop,
        schurMultiplierRank m = fiberCount m * (fiberCount m + 1) / 2 := by
    filter_upwards [hLower, hProduct] with m hmLower hmProduct
    rw [hmProduct hmLower,
      conclusion_binfold_gauge_schur_multiplier_quadratic_explosion_productRank_eq]
  exact eventually_atTop.1 hevent

end Omega.Conclusion
