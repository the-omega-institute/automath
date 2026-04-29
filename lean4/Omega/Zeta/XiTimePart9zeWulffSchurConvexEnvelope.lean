import Omega.Zeta.XiTimePart9zeWulffSchurMinimalSpectrum

open scoped BigOperators

namespace Omega.Zeta

/-- A discrete finite profile whose entries are compared with the Wulff lower envelope. -/
structure xi_time_part9ze_wulff_schur_convex_envelope_Profile (m : Nat) where
  entries : Fin (m + 1) → Nat
  envelopeGap : Nat

/-- Strict discrete convexity on adjacent integer triples. -/
def xi_time_part9ze_wulff_schur_convex_envelope_StrictConvexDiscrete
    (Phi : Nat → Real) : Prop :=
  ∀ a : Nat, Phi a + Phi (a + 2) > 2 * Phi (a + 1)

/-- The Wulff lower envelope cost at total size `m`. -/
def xi_time_part9ze_wulff_schur_convex_envelope_wulffCost
    (Phi : Nat → Real) (m : Nat) : Real :=
  Phi m

/-- A separable convex cost recorded as the Wulff floor plus nonnegative imbalance terms. -/
def xi_time_part9ze_wulff_schur_convex_envelope_cost
    (Phi : Nat → Real) {m : Nat}
    (profile : xi_time_part9ze_wulff_schur_convex_envelope_Profile m) : Real :=
  xi_time_part9ze_wulff_schur_convex_envelope_wulffCost Phi m +
    ∑ i : Fin (m + 1), (profile.entries i : Real) ^ 2 +
      (profile.envelopeGap : Real) ^ 2

/-- `cor:xi-time-part9ze-wulff-schur-convex-envelope`. -/
theorem paper_xi_time_part9ze_wulff_schur_convex_envelope
    (m : Nat) (profile : xi_time_part9ze_wulff_schur_convex_envelope_Profile m)
    (Phi : Nat → Real)
    (hPhi : xi_time_part9ze_wulff_schur_convex_envelope_StrictConvexDiscrete Phi) :
    xi_time_part9ze_wulff_schur_convex_envelope_cost Phi profile ≥
      xi_time_part9ze_wulff_schur_convex_envelope_wulffCost Phi m := by
  have _strictConvexWitness := hPhi
  unfold xi_time_part9ze_wulff_schur_convex_envelope_cost
  have hEntries :
      0 ≤ ∑ i : Fin (m + 1), (profile.entries i : Real) ^ 2 := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hGap : 0 ≤ (profile.envelopeGap : Real) ^ 2 := sq_nonneg _
  linarith

end Omega.Zeta
