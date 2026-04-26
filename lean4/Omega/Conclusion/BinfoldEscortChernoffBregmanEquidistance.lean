import Mathlib.Tactic
import Omega.Zeta.XiTimePart9sbEscortChernoffSaddle

namespace Omega.Conclusion

open Omega.Zeta

noncomputable section

/-- Quadratic Bregman divergence attached to the escort potential `ψ(r) = log A(r)`. -/
def binfoldEscortBregman (a b x y : ℝ) : ℝ :=
  xiTimePart9sbPsi a b x - xiTimePart9sbPsi a b y - xiTimePart9sbTheta a b y * (x - y)

/-- Jensen gap at the midpoint of the bin-fold escort chord. -/
def binfoldEscortJensenGap (a b p q : ℝ) : ℝ :=
  (xiTimePart9sbPsi a b p + xiTimePart9sbPsi a b q) / 2 - xiTimePart9sbPsi a b ((p + q) / 2)

private lemma binfoldEscortBregman_eq (a b x y : ℝ) :
    binfoldEscortBregman a b x y = b * (x - y) ^ 2 := by
  rw [binfoldEscortBregman]
  simp [xiTimePart9sbPsi_eq, xiTimePart9sbTheta]
  ring

private lemma binfoldEscortJensenGap_eq (a b p q : ℝ) :
    binfoldEscortJensenGap a b p q = xiTimePart9sbChernoffInfo b p q := by
  rw [binfoldEscortJensenGap, xiTimePart9sbChernoffInfo]
  simp [xiTimePart9sbPsi_eq]
  ring

/-- Paper label: `thm:conclusion-binfold-escort-chernoff-bregman-equidistance`. Specializing the
quadratic escort saddle theorem to the secant slope on `[p,q]`, the midpoint is the unique saddle,
the two endpoint-to-midpoint Bregman divergences agree, and their common value is both the
midpoint Jensen gap and the closed Chernoff information. -/
theorem paper_conclusion_binfold_escort_chernoff_bregman_equidistance
    (a b p q : ℝ) (hb : 0 < b) (hpq : p < q) :
    let rStar : ℝ := (p + q) / 2
    let c := xiTimePart9sbSecantSlope a b p q
    xiTimePart9sbTheta a b rStar = c ∧
      binfoldEscortBregman a b p rStar = binfoldEscortBregman a b q rStar ∧
      binfoldEscortBregman a b p rStar = binfoldEscortJensenGap a b p q ∧
      binfoldEscortBregman a b p rStar = xiTimePart9sbChernoffInfo b p q := by
  dsimp
  have hsaddle := paper_xi_time_part9sb_escort_chernoff_saddle a b p q hb hpq
  dsimp at hsaddle
  rcases hsaddle with ⟨htheta, _hmono, _hcrit, _hmax, _huniq, _hchernoff⟩
  have hpoint : xiTimePart9sbPoint p q (1 / 2) = (p + q) / 2 := by
    dsimp [xiTimePart9sbPoint]
    ring
  have htheta' : xiTimePart9sbTheta a b ((p + q) / 2) = xiTimePart9sbSecantSlope a b p q := by
    rw [← hpoint]
    exact htheta
  refine ⟨htheta', ?_, ?_, ?_⟩
  · rw [binfoldEscortBregman_eq, binfoldEscortBregman_eq]
    ring
  · rw [binfoldEscortBregman_eq, binfoldEscortJensenGap_eq, xiTimePart9sbChernoffInfo]
    ring
  · rw [binfoldEscortBregman_eq, xiTimePart9sbChernoffInfo]
    ring

end

end Omega.Conclusion
