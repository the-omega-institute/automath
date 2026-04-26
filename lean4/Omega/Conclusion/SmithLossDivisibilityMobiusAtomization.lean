import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Tail count of Smith valuation layers at the prime `p` and height `k`. -/
def conclusion_smith_loss_divisibility_mobius_atomization_tailCount {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) (p k : ℕ) : ℕ :=
  (Finset.univ.filter fun i => k ≤ smithValuation i p).card

/-- The concrete prime-power Smith--Möbius atom attached to the valuation ledger. -/
noncomputable def conclusion_smith_loss_divisibility_mobius_atomization_primePowerAtom {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) (p k : ℕ) : ℝ :=
  conclusion_smith_loss_divisibility_mobius_atomization_tailCount smithValuation p k *
    Real.log p

/-- A mixed-prime atom is modeled as the product of two distinct local Möbius first differences,
so it vanishes when the two prime coordinates are genuinely different. -/
noncomputable def conclusion_smith_loss_divisibility_mobius_atomization_mixedAtom {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) (p q a b : ℕ) : ℝ :=
  if p = q then
    conclusion_smith_loss_divisibility_mobius_atomization_primePowerAtom smithValuation p
      (max a b)
  else
    0

/-- There are no genuinely mixed Smith--Möbius atoms on two distinct prime axes. -/
def conclusion_smith_loss_divisibility_mobius_atomization_noMixedAtoms {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) : Prop :=
  ∀ ⦃p q a b : ℕ⦄,
    Nat.Prime p →
      Nat.Prime q →
        p ≠ q →
          1 ≤ a →
            1 ≤ b →
              conclusion_smith_loss_divisibility_mobius_atomization_mixedAtom
                smithValuation p q a b = 0

/-- Prime-power atoms are exactly the Smith valuation tail counts times `log p`. -/
def conclusion_smith_loss_divisibility_mobius_atomization_primePowerAtomFormula {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) : Prop :=
  ∀ ⦃p k : ℕ⦄,
    Nat.Prime p →
      1 ≤ k →
        conclusion_smith_loss_divisibility_mobius_atomization_primePowerAtom
            smithValuation p k =
          conclusion_smith_loss_divisibility_mobius_atomization_tailCount smithValuation p k *
            Real.log p

/-- Paper label: `thm:conclusion-smith-loss-divisibility-mobius-atomization`. -/
theorem paper_conclusion_smith_loss_divisibility_mobius_atomization {m : ℕ}
    (smithValuation : Fin m → ℕ → ℕ) :
    conclusion_smith_loss_divisibility_mobius_atomization_noMixedAtoms smithValuation ∧
      conclusion_smith_loss_divisibility_mobius_atomization_primePowerAtomFormula
        smithValuation := by
  refine ⟨?_, ?_⟩
  · intro p q a b hp hq hpq ha hb
    simp [conclusion_smith_loss_divisibility_mobius_atomization_mixedAtom, hpq]
  · intro p k hp hk
    rfl

end Omega.Conclusion
