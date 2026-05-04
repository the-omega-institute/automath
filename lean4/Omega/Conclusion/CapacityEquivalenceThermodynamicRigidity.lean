import Mathlib.Tactic
import Omega.Conclusion.CapacityRamanujanPlateauLaw
import Omega.Zeta.LocalInversionDelta

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- Paper label: `thm:conclusion-capacity-equivalence-thermodynamic-rigidity`. -/
theorem paper_conclusion_capacity_equivalence_thermodynamic_rigidity
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (d : X → ℕ) (e : Y → ℕ)
    (hposd : ∀ x, 0 < d x) (hpose : ∀ y, 0 < e y)
    (hcap : ∀ T : ℕ, (∑ x, min (d x) T) = (∑ y, min (e y) T)) :
    ∀ k : ℕ,
      (Finset.univ.filter (fun x : X => d x = k)).card =
        (Finset.univ.filter (fun y : Y => e y = k)).card := by
  classical
  have htail :
      ∀ s : ℕ, 1 ≤ s →
        (Finset.univ.filter (fun x : X => s ≤ d x)).card =
          (Finset.univ.filter (fun y : Y => s ≤ e y)).card := by
    intro s hs
    have hdelta :
        CapacityRamanujanPlateauLaw.deltaCapacity d s =
          CapacityRamanujanPlateauLaw.deltaCapacity e s := by
      unfold CapacityRamanujanPlateauLaw.deltaCapacity
        CapacityRamanujanPlateauLaw.capacityCurve
      rw [hcap s, hcap (s - 1)]
    have hdcard :
        CapacityRamanujanPlateauLaw.deltaCapacity d s =
          (Finset.univ.filter (fun x : X => s ≤ d x)).card := by
      rw [CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge d s hs]
      exact
        Fintype.card_of_subtype (Finset.univ.filter fun x : X => s ≤ d x) (by
          intro x
          simp)
    have hecard :
        CapacityRamanujanPlateauLaw.deltaCapacity e s =
          (Finset.univ.filter (fun y : Y => s ≤ e y)).card := by
      rw [CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge e s hs]
      exact
        Fintype.card_of_subtype (Finset.univ.filter fun y : Y => s ≤ e y) (by
          intro y
          simp)
    rw [← hdcard, hdelta, hecard]
  intro k
  by_cases hk0 : k = 0
  · subst hk0
    have hd0 : (Finset.univ.filter (fun x : X => d x = 0)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext x
      simp [Nat.ne_of_gt (hposd x)]
    have he0 : (Finset.univ.filter (fun y : Y => e y = 0)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext y
      simp [Nat.ne_of_gt (hpose y)]
    rw [hd0, he0]
  · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
    calc
      (Finset.univ.filter (fun x : X => d x = k)).card
          =
          (Finset.univ.filter (fun x : X => k ≤ d x)).card -
            (Finset.univ.filter (fun x : X => k + 1 ≤ d x)).card := by
            symm
            exact
              Omega.Zeta.LocalInversionDelta.filter_ge_card_sub_succ
                (S := (Finset.univ : Finset X)) d k
      _ =
          (Finset.univ.filter (fun y : Y => k ≤ e y)).card -
            (Finset.univ.filter (fun y : Y => k + 1 ≤ e y)).card := by
            rw [htail k hk1, htail (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
      _ = (Finset.univ.filter (fun y : Y => e y = k)).card := by
            exact
              Omega.Zeta.LocalInversionDelta.filter_ge_card_sub_succ
                (S := (Finset.univ : Finset Y)) e k

end Omega.Conclusion
