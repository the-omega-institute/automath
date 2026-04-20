import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Omega.Folding.FiberArithmetic
import Omega.Folding.MultinomialVpCarrySignature

namespace Omega.Folding

/-- The pointwise `v₂`-gain attached to doubling a fiber multiplicity. -/
noncomputable def fiberGaugeDoublingV2Term {m : ℕ} (x : Omega.X m) : ℕ :=
  padicValNat 2 ((2 * Omega.X.fiberMultiplicity x).factorial) -
    2 * padicValNat 2 ((Omega.X.fiberMultiplicity x).factorial)

/-- Concrete package for the dyadic digit-sum identity behind fiber-gauge volume doubling:
the pointwise Legendre difference equals the binary digit sum, and summing over `x : X m`
recovers the fold-wide identity.
    prop:fiber-gauge-volume-doubling-v2-digit-sum -/
def FiberGaugeVolumeDoublingV2DigitSumSpec (m : ℕ) : Prop :=
  (∀ x : Omega.X m, fiberGaugeDoublingV2Term x = basePDigitSum 2 (Omega.X.fiberMultiplicity x)) ∧
    ((Finset.univ : Finset (Omega.X m)).sum (fun x => fiberGaugeDoublingV2Term (m := m) x) =
      Finset.univ.sum (fun x : Omega.X m => basePDigitSum 2 (Omega.X.fiberMultiplicity x)))

private lemma basePDigitSum_two_mul (n : ℕ) : basePDigitSum 2 (2 * n) = basePDigitSum 2 n := by
  by_cases hn : n = 0
  · simp [hn, basePDigitSum]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    rw [basePDigitSum]
    simpa [pow_one, List.sum_append, two_mul] using
      congrArg List.sum (Nat.digits_base_pow_mul (b := 2) (k := 1) (m := n) one_lt_two hn_pos)

private lemma fiberGaugeDoublingV2Term_eq_digitSum {m : ℕ} (x : Omega.X m) :
    fiberGaugeDoublingV2Term x = basePDigitSum 2 (Omega.X.fiberMultiplicity x) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let d := Omega.X.fiberMultiplicity x
  let s := basePDigitSum 2 d
  have hdouble :
      padicValNat 2 ((2 * d).factorial) = 2 * d - basePDigitSum 2 (2 * d) := by
    simpa [basePDigitSum] using
      (sub_one_mul_padicValNat_factorial (p := 2) (n := 2 * d))
  have hsingle :
      padicValNat 2 (d.factorial) = d - s := by
    simpa [basePDigitSum] using
      (sub_one_mul_padicValNat_factorial (p := 2) (n := d))
  have hs_le : s ≤ d := by
    simpa [d, s, basePDigitSum] using Nat.digit_sum_le 2 d
  simp only [d, s] at hdouble hsingle hs_le ⊢
  rw [fiberGaugeDoublingV2Term, hdouble, hsingle, basePDigitSum_two_mul]
  omega

theorem paper_fiber_gauge_volume_doubling_v2_digit_sum (m : ℕ) :
    FiberGaugeVolumeDoublingV2DigitSumSpec m := by
  refine ⟨fiberGaugeDoublingV2Term_eq_digitSum, ?_⟩
  simpa using
    (Finset.sum_congr rfl fun x _ => fiberGaugeDoublingV2Term_eq_digitSum (m := m) x :
      (Finset.univ : Finset (Omega.X m)).sum (fun x => fiberGaugeDoublingV2Term (m := m) x) =
        (Finset.univ : Finset (Omega.X m)).sum
          (fun x => basePDigitSum 2 (Omega.X.fiberMultiplicity x)))

end Omega.Folding
