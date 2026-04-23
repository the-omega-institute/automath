import Mathlib.Tactic
import Omega.POM.MultiplicityCompositionMod3Sparsity
import Omega.POM.MultiplicityCompositionSharpMainTermConstant

namespace Omega.POM

noncomputable section

/-- Concrete simple-pole package extracted from the existing multiplicity-composition root and
the mod-`3` sparsity estimate. The support witness `2, 3` records the aperiodicity proxy, while
the already verified sharp-main-term theorem supplies the positive simple root and residue data. -/
def pom_multiplicity_composition_mod3_simple_pole_u_statement (q : ℕ) : Prop :=
  0 < pomMultiplicityCompositionRho q ∧
    pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q) = 1 ∧
    (∀ t : ℝ,
      0 < t →
        pomMultiplicityCompositionAtomicSeries q t = 1 →
          t = pomMultiplicityCompositionRho q) ∧
    0 < pomMultiplicityCompositionAtomicSeriesDerivAt q (pomMultiplicityCompositionRho q) ∧
    Nat.gcd 2 3 = 1 ∧
    pomMultiplicityCompositionMainTermConstant q = 1 / pomMultiplicityCompositionRenewalMean q ∧
    0 < mod3SparseEta ∧
    mod3SparseEta < 1

private theorem pom_multiplicity_composition_mod3_simple_pole_u_root_unique
    (q : ℕ) {t : ℝ} (ht : 0 < t) (hroot : pomMultiplicityCompositionAtomicSeries q t = 1) :
    t = pomMultiplicityCompositionRho q := by
  have hρroot :
      pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q) = 1 :=
    (paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.2.1 q).1
  have hw : 0 < pomMomentHierarchyWeight q := by
    unfold pomMomentHierarchyWeight
    positivity
  have hρpos : 0 < pomMultiplicityCompositionRho q :=
    (paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.1 q).1
  by_cases hEq : t = pomMultiplicityCompositionRho q
  · exact hEq
  · have hlt_or_gt :
        t < pomMultiplicityCompositionRho q ∨ pomMultiplicityCompositionRho q < t :=
      lt_or_gt_of_ne hEq
    cases hlt_or_gt with
    | inl hlt =>
        have hsum :
            t + t ^ (2 : Nat) <
              pomMultiplicityCompositionRho q + pomMultiplicityCompositionRho q ^ (2 : Nat) := by
          nlinarith [ht, hρpos, hlt]
        have hstrict :
            pomMultiplicityCompositionAtomicSeries q t <
              pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q) := by
          have hmul :=
            mul_lt_mul_of_pos_left hsum hw
          calc
            pomMultiplicityCompositionAtomicSeries q t
                = pomMomentHierarchyWeight q * (t + t ^ (2 : Nat)) := by
                    unfold pomMultiplicityCompositionAtomicSeries
                    ring
            _ < pomMomentHierarchyWeight q *
                  (pomMultiplicityCompositionRho q + pomMultiplicityCompositionRho q ^ (2 : Nat)) :=
                  hmul
            _ = pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q) := by
                  unfold pomMultiplicityCompositionAtomicSeries
                  ring
        have : (1 : ℝ) < 1 := by simpa [hroot, hρroot] using hstrict
        linarith
    | inr hgt =>
        have hsum :
            pomMultiplicityCompositionRho q + pomMultiplicityCompositionRho q ^ (2 : Nat) <
              t + t ^ (2 : Nat) := by
          nlinarith [ht, hρpos, hgt]
        have hstrict :
            pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q) <
              pomMultiplicityCompositionAtomicSeries q t := by
          have hmul :=
            mul_lt_mul_of_pos_left hsum hw
          calc
            pomMultiplicityCompositionAtomicSeries q (pomMultiplicityCompositionRho q)
                = pomMomentHierarchyWeight q *
                    (pomMultiplicityCompositionRho q + pomMultiplicityCompositionRho q ^ (2 : Nat)) := by
                      unfold pomMultiplicityCompositionAtomicSeries
                      ring
            _ < pomMomentHierarchyWeight q * (t + t ^ (2 : Nat)) := hmul
            _ = pomMultiplicityCompositionAtomicSeries q t := by
                  unfold pomMultiplicityCompositionAtomicSeries
                  ring
        have : (1 : ℝ) < 1 := by simpa [hroot, hρroot] using hstrict
        linarith

/-- The positive root for the simplified two-step atomic series is unique by monotonicity on the
positive half-line; the derivative at the root is positive, the step support `{2, 3}` is
aperiodic, and the same package carries the residue-style main-term constant together with the
uniform mod-`3` exponential control. -/
theorem pom_multiplicity_composition_mod3_simple_pole_u_true (q : ℕ) :
    pom_multiplicity_composition_mod3_simple_pole_u_statement q := by
  rcases paper_pom_multiplicity_composition_mod3_sparsity with ⟨heta_pos, heta_lt_one, _⟩
  refine
    ⟨(paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.1 q).1,
      (paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.2.1 q).1,
      ?_,
      paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.2.2.1 q,
      by decide,
      (paper_pom_multiplicity_composition_sharp_main_term_constant.2.2.2.2.2 q).2,
      heta_pos,
      heta_lt_one⟩
  intro t ht hroot
  exact pom_multiplicity_composition_mod3_simple_pole_u_root_unique q ht hroot

/-- Paper label: `thm:pom-multiplicity-composition-mod3-simple-pole-u`. -/
def paper_pom_multiplicity_composition_mod3_simple_pole_u (q : ℕ) : Prop := by
  exact pom_multiplicity_composition_mod3_simple_pole_u_statement q

end

end Omega.POM
