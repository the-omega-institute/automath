import Mathlib.Tactic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree

namespace Omega.CircleDimension.SquarefreeMedianDistance

open Nat Finset
open scoped symmDiff

/-- Number of distinct prime factors.
    thm:cdim-median-godel-distance-median-closed-form -/
def omegaPrime (n : ℕ) : ℕ := n.primeFactors.card

/-- For squarefree `a, b`, the prime factors of `(a/gcd) * (b/gcd)` form the
    symmetric difference of `a.primeFactors` and `b.primeFactors`.
    thm:cdim-median-godel-distance-median-closed-form -/
theorem primeFactors_quotient_product
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ((a / Nat.gcd a b) * (b / Nat.gcd a b)).primeFactors =
      a.primeFactors ∆ b.primeFactors := by
  -- a / gcd has prime factors a.pf \ b.pf  (using primeFactors_div_gcd)
  have h1 : (a / Nat.gcd a b).primeFactors = a.primeFactors \ b.primeFactors :=
    Nat.primeFactors_div_gcd ha hb0
  -- b / gcd has prime factors b.pf \ a.pf  (note: gcd b a = gcd a b)
  have h2 : (b / Nat.gcd a b).primeFactors = b.primeFactors \ a.primeFactors := by
    rw [Nat.gcd_comm]
    exact Nat.primeFactors_div_gcd hb ha0
  -- The two factors are coprime, so primeFactors of product = union
  have ha_div_pos : a / Nat.gcd a b ≠ 0 := by
    have hgcd_pos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha0)
    have : Nat.gcd a b ∣ a := Nat.gcd_dvd_left _ _
    have hpos : 0 < a / Nat.gcd a b := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) this) hgcd_pos
    exact Nat.pos_iff_ne_zero.mp hpos
  have hb_div_pos : b / Nat.gcd a b ≠ 0 := by
    have hgcd_pos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hb0)
    have : Nat.gcd a b ∣ b := Nat.gcd_dvd_right _ _
    have hpos : 0 < b / Nat.gcd a b :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) this) hgcd_pos
    exact Nat.pos_iff_ne_zero.mp hpos
  rw [Nat.primeFactors_mul ha_div_pos hb_div_pos]
  rw [h1, h2]
  -- Need: (a.pf \ b.pf) ∪ (b.pf \ a.pf) = a.pf ∆ b.pf
  rw [symmDiff_def, Finset.sup_eq_union]

/-- Paper package: `ω((a/gcd)·(b/gcd)) = |a.pf △ b.pf|` for squarefree `a, b`.
    thm:cdim-median-godel-distance-median-closed-form -/
theorem paper_cdim_median_godel_distance_squarefree
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    omegaPrime ((a / Nat.gcd a b) * (b / Nat.gcd a b)) =
      (a.primeFactors ∆ b.primeFactors).card := by
  unfold omegaPrime
  rw [primeFactors_quotient_product ha hb ha0 hb0]

end Omega.CircleDimension.SquarefreeMedianDistance
