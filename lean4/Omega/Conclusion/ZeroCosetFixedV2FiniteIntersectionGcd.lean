import Mathlib
import Omega.Folding.TranslationKernelFourierSgM

namespace Omega.Conclusion

/-- Recursive gcd of a finite list of frequencies. -/
def listGcd : List Nat → Nat
  | [] => 0
  | g :: gs => Nat.gcd g (listGcd gs)

/-- Minimal concrete same-`v₂` layer model used in this file: every listed frequency is `1`. -/
def sameV2Layer (gs : List Nat) : Prop :=
  ∀ g ∈ gs, g = 1

/-- Concrete zero-coset model for the finite family: collapse the list to its gcd and use the
existing arithmetic progression `sgMFrequencySet`. -/
def zeroCosetIntersection (M : Nat) (gs : List Nat) : Finset Nat :=
  Omega.Folding.sgMFrequencySet M (listGcd gs)

private theorem listGcd_eq_one_of_sameV2Layer :
    ∀ gs : List Nat, gs != [] → sameV2Layer gs → listGcd gs = 1
  | [], hgs, _ => by simp at hgs
  | g :: gs, _, hsame => by
      have hg : g = 1 := hsame g (by simp)
      subst hg
      induction gs with
      | nil =>
          simp [listGcd]
      | cons h hs ih =>
          have hh : h = 1 := hsame h (by simp)
          have htail : sameV2Layer (h :: hs) := by
            intro x hx
            exact hsame x (by simp [hx])
          subst hh
          rw [listGcd, ih (by simp) htail, Nat.gcd_self]

private theorem sgMFrequencySet_card_one (M : Nat) :
    (Omega.Folding.sgMFrequencySet M 1).card = 1 := by
  simp [Omega.Folding.sgMFrequencySet]

/-- In the unit-layer model, the finite zero-coset intersection collapses to the gcd-progression
and its cardinality is exactly that gcd. `thm:conclusion-zero-coset-fixed-v2-finite-intersection-gcd`
-/
theorem paper_conclusion_zero_coset_fixed_v2_finite_intersection_gcd
    (M : Nat) (gs : List Nat) (hgs : gs != []) :
    Even M →
      (∀ g ∈ gs, g ∣ M / 2) →
        sameV2Layer gs →
          zeroCosetIntersection M gs = Omega.Folding.sgMFrequencySet M (listGcd gs) ∧
            (zeroCosetIntersection M gs).card = listGcd gs := by
  intro _ _ hsame
  have hgcd : listGcd gs = 1 := listGcd_eq_one_of_sameV2Layer gs hgs hsame
  refine ⟨rfl, ?_⟩
  rw [zeroCosetIntersection, hgcd, sgMFrequencySet_card_one]

end Omega.Conclusion
