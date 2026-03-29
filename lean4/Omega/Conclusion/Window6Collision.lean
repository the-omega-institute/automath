import Mathlib.Tactic

/-! ### Window-6 q-moment spectrum and collision probability

Arithmetic certificates for the conclusion chapter:
q-moment triple from histogram {2:8, 3:4, 4:9}, collision probability reduction,
and related Wedderburn dimension identities. -/

namespace Omega.Conclusion

-- ══════════════════════════════════════════════════════════════
-- Phase R130: Window-6 q-moment spectrum triple
-- ══════════════════════════════════════════════════════════════

/-- Window-6 q-moment spectrum from histogram {2:8, 3:4, 4:9}.
    S_0=21, S_1=64, S_2=212.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_qmoment_triple :
    8 + 4 + 9 = 21 ∧
    8 * 2 + 4 * 3 + 9 * 4 = 64 ∧
    8 * 4 + 4 * 9 + 9 * 16 = 212 := by omega

/-- S_2(6) = Σ d(w)² = Wedderburn dimension 212.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_S2_wedderburn :
    8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2 = 212 := by omega

/-- Likelihood ratio monotonicity: sector weights shift toward large fibers.
    thm:conclusion-window6-qmoment-triple-geometry -/
theorem window6_likelihood_shift :
    9 * 16 * 21 > 9 * 4 * 64 ∧ 9 * 4 * 21 > 9 * 1 * 64 := by omega

/-- Paper: thm:conclusion-window6-qmoment-triple-geometry -/
theorem paper_window6_qmoment_triple :
    8 + 4 + 9 = 21 ∧ 8 * 2 + 4 * 3 + 9 * 4 = 64 ∧ 8 * 4 + 4 * 9 + 9 * 16 = 212 :=
  window6_qmoment_triple

-- ══════════════════════════════════════════════════════════════
-- Phase R130: Window-6 collision probability rational form
-- ══════════════════════════════════════════════════════════════

/-- Collision probability fraction: 212/4096 = 53/1024.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_prob_reduced :
    212 * 1024 = 53 * 4096 := by omega

/-- GCD reduction factor.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_gcd : Nat.gcd 212 4096 = 4 := by native_decide

/-- Microstate count squared: 64² = 4096.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_microstate_sq : 64 ^ 2 = 4096 := by omega

/-- Reduced fraction components.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_components :
    212 / 4 = 53 ∧ 4096 / 4 = 1024 := by omega

/-- Collision dimension exceeds 3× microstate count.
    thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem window6_collision_exceeds_linear : 212 > 3 * 64 := by omega

/-- Paper: thm:conclusion-window6-groupoid-collision-dimension-identity -/
theorem paper_window6_collision_prob :
    212 * 1024 = 53 * 4096 := window6_collision_prob_reduced

-- ══════════════════════════════════════════════════════════════
-- Phase R136: Quadratic residues mod 21
-- ══════════════════════════════════════════════════════════════

/-- Decidable predicate: is a a nonzero quadratic residue mod 21? -/
def isNonzeroQR21 (a : Nat) : Bool :=
  a != 0 && (List.range 21).any (fun x => x * x % 21 == a)

/-- Number of nonzero quadratic residues in Z/21Z equals 7.
    prop:conclusion-window6-crt-euler-phi -/
theorem quadratic_residues_mod21 :
    ((Finset.range 21).filter (fun a => isNonzeroQR21 a)).card = 7 := by native_decide

/-- The nonzero QRs mod 21 are {1, 4, 7, 9, 15, 16, 18}.
    prop:conclusion-window6-crt-euler-phi -/
theorem quadratic_residues_mod21_explicit :
    (Finset.range 21).filter (fun a => isNonzeroQR21 a) = {1, 4, 7, 9, 15, 16, 18} := by
  native_decide

/-- Paper: prop:conclusion-window6-crt-euler-phi -/
theorem paper_quadratic_residues_mod21 :
    ((Finset.range 21).filter (fun a => isNonzeroQR21 a)).card = 7 :=
  quadratic_residues_mod21

-- ══════════════════════════════════════════════════════════════
-- Phase R138: Window-8 histogram consistency + higher moments
-- ══════════════════════════════════════════════════════════════

/-- Window-8 bin-fold histogram {3:21, 5:11, 6:23} consistency checks.
    thm:conclusion-window8-groupoid-collision-dimension-identity -/
theorem window8_histogram_consistency :
    21 + 11 + 23 = 55 ∧ 21 * 3 + 11 * 5 + 23 * 6 = 256 := by omega

/-- Higher moment sums from window-8 histogram.
    thm:conclusion-window8-groupoid-collision-dimension-identity -/
theorem window8_higher_moments :
    21 * 3 ^ 3 + 11 * 5 ^ 3 + 23 * 6 ^ 3 = 6910 ∧
    21 * 3 ^ 4 + 11 * 5 ^ 4 + 23 * 6 ^ 4 = 38384 ∧
    21 * 3 ^ 5 + 11 * 5 ^ 5 + 23 * 6 ^ 5 = 218326 := by omega

/-- Paper: thm:conclusion-window8-groupoid-collision-dimension-identity -/
theorem paper_window8_higher_moments :
    21 * 3 ^ 3 + 11 * 5 ^ 3 + 23 * 6 ^ 3 = 6910 ∧
    21 * 3 ^ 4 + 11 * 5 ^ 4 + 23 * 6 ^ 4 = 38384 ∧
    21 * 3 ^ 5 + 11 * 5 ^ 5 + 23 * 6 ^ 5 = 218326 :=
  window8_higher_moments

end Omega.Conclusion
