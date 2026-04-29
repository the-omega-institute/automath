import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.MultinomialVpCarrySignature

namespace Omega.Conclusion

open scoped BigOperators

section

variable {W : Type} [Fintype W] [DecidableEq W]
variable {A : W → Type} [∀ w, Fintype (A w)] [∀ w, DecidableEq (A w)]

/-- The doubled coarse gauge volume `∏_w (2 d_m(w))!`. -/
def multiscaleCoarseGaugeVolume (d : W → ℕ) : ℚ :=
  ∏ w, (Nat.factorial (2 * d w) : ℚ)

/-- The refined gauge volume `∏_w ∏_{u ∈ r⁻¹(w)} d_{m+1}(u)!`. -/
def multiscaleFineGaugeVolume (e : (w : W) → A w → ℕ) : ℚ :=
  ∏ w, ∏ u, (Nat.factorial (e w u) : ℚ)

/-- The local multinomial coefficient attached to the refined fiber over `w`. -/
def multiscaleLocalRefinementCoeff (e : (w : W) → A w → ℕ) (w : W) : ℕ :=
  Nat.multinomial (Finset.univ : Finset (A w)) (e w)

/-- The total `p`-adic multiscale defect. -/
def multiscaleCarryDefect (p : ℕ) (d : W → ℕ) (e : (w : W) → A w → ℕ) : ℤ :=
  padicValRat p (multiscaleCoarseGaugeVolume d / multiscaleFineGaugeVolume e)

/-- The local `p`-adic carry contribution at the coarse fiber `w`. -/
def multiscaleLocalCarry (p : ℕ) (e : (w : W) → A w → ℕ) (w : W) : ℤ :=
  padicValRat p (multiscaleLocalRefinementCoeff e w : ℚ)

/-- Paper-facing multiscale carry-defect identity: when each coarse fiber splits into a finite
cluster of refined fibers with total size `2 d_m(w)`, the global gauge-volume quotient factors as
the product of the local multinomial coefficients, and the corresponding `p`-adic defect is the
sum of the local `p`-adic carry counts.
    thm:fold-multiscale-carry-defect -/
theorem paper_fold_multiscale_carry_defect
    (p : ℕ) (hp : Nat.Prime p) (d : W → ℕ) (e : (w : W) → A w → ℕ)
    (hcompat : ∀ w, ∑ u, e w u = 2 * d w) :
    multiscaleCoarseGaugeVolume d / multiscaleFineGaugeVolume e =
        ∏ w, (multiscaleLocalRefinementCoeff e w : ℚ) ∧
      multiscaleCarryDefect p d e = ∑ w, multiscaleLocalCarry p e w := by
  have hlocal :
      ∀ w,
        (∏ u, (Nat.factorial (e w u) : ℚ)) *
            (multiscaleLocalRefinementCoeff e w : ℚ) =
          (Nat.factorial (2 * d w) : ℚ) := by
    intro w
    exact_mod_cast
      (by simpa [multiscaleLocalRefinementCoeff, hcompat w] using
        (Nat.multinomial_spec (s := (Finset.univ : Finset (A w))) (f := e w)))
  have hfactor :
      multiscaleFineGaugeVolume e * ∏ w, (multiscaleLocalRefinementCoeff e w : ℚ) =
        multiscaleCoarseGaugeVolume d := by
    unfold multiscaleFineGaugeVolume multiscaleCoarseGaugeVolume
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro w hw
    simpa using hlocal w
  have hfine_ne : multiscaleFineGaugeVolume e ≠ 0 := by
    unfold multiscaleFineGaugeVolume
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro w hw
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro u hu
    exact_mod_cast Nat.factorial_ne_zero (e w u)
  have hcoeff_ne : ∀ w, (multiscaleLocalRefinementCoeff e w : ℚ) ≠ 0 := by
    intro w
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos (s := (Finset.univ : Finset (A w))) (f := e w)))
  have hquot :
      multiscaleCoarseGaugeVolume d / multiscaleFineGaugeVolume e =
        ∏ w, (multiscaleLocalRefinementCoeff e w : ℚ) := by
    apply (div_eq_iff hfine_ne).2
    simpa [mul_comm] using hfactor.symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hval :
      padicValRat p (∏ w, (multiscaleLocalRefinementCoeff e w : ℚ)) =
        ∑ w, padicValRat p (multiscaleLocalRefinementCoeff e w : ℚ) := by
    classical
    refine Finset.induction ?_ ?_ (Finset.univ : Finset W)
    · simp [padicValRat.one]
    · intro w s hw hs
      rw [Finset.prod_insert hw, Finset.sum_insert hw]
      rw [padicValRat.mul (hcoeff_ne w)]
      · simpa using hs
      · exact Finset.prod_ne_zero_iff.mpr (fun a ha => hcoeff_ne a)
  constructor
  · exact hquot
  · unfold multiscaleCarryDefect multiscaleLocalCarry
    rw [hquot, hval]

/-- The local refined multiplicity profile over the coarse fiber `w`, recorded as a list. -/
noncomputable def fold_multiscale_carry_defect_digit_sum_log_gap_localProfile
    (e : (w : W) → A w → ℕ) (w : W) : List ℕ :=
  ((Finset.univ : Finset (A w)).toList.map (e w))

/-- Paper-facing corollary: the multiscale carry defect still factors as the sum of the local
`p`-adic carries, each local carry-count model is the corresponding digit-sum excess, and any
finite prime-log bookkeeping sum can therefore be rewritten in digit-sum form.
    cor:fold-multiscale-carry-defect-digit-sum-log-gap -/
theorem paper_fold_multiscale_carry_defect_digit_sum_log_gap
    (p : ℕ) [Fact p.Prime] (d : W → ℕ) (e : (w : W) → A w → ℕ)
    (hcompat : ∀ w, ∑ u, e w u = 2 * d w) :
    (multiscaleCarryDefect p d e = ∑ w, multiscaleLocalCarry p e w) ∧
      (∀ w,
          Omega.Folding.multinomialCarryCount p
              (fold_multiscale_carry_defect_digit_sum_log_gap_localProfile e w) =
            Omega.Folding.multinomialLegendreDigitExcess p
              (fold_multiscale_carry_defect_digit_sum_log_gap_localProfile e w)) ∧
  ((((∑ w,
            Omega.Folding.multinomialCarryCount p
              (fold_multiscale_carry_defect_digit_sum_log_gap_localProfile e w)) : ℤ) : ℝ) *
          Real.log p =
        (((∑ w,
            Omega.Folding.multinomialLegendreDigitExcess p
              (fold_multiscale_carry_defect_digit_sum_log_gap_localProfile e w)) : ℤ) : ℝ) *
          Real.log p) := by
  constructor
  · exact (paper_fold_multiscale_carry_defect p (Fact.out : Nat.Prime p) d e hcompat).2
  constructor
  · intro w
    exact (Omega.Folding.paper_multinomial_vp_carry_signature p
      (fold_multiscale_carry_defect_digit_sum_log_gap_localProfile e w)).2
  · have hsum :
        (∑ w,
            Omega.Folding.multinomialCarryCount p
              (fold_multiscale_carry_defect_digit_sum_log_gap_localProfile e w)) =
          ∑ w,
            Omega.Folding.multinomialLegendreDigitExcess p
              (fold_multiscale_carry_defect_digit_sum_log_gap_localProfile e w) := by
        refine Finset.sum_congr rfl ?_
        intro w hw
        exact (Omega.Folding.paper_multinomial_vp_carry_signature p
          (fold_multiscale_carry_defect_digit_sum_log_gap_localProfile e w)).2
    exact congrArg (fun z : ℤ => (z : ℝ) * Real.log p) hsum

end

end Omega.Conclusion
