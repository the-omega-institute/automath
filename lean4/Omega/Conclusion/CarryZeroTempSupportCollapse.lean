import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The mass that a zero-temperature limit assigns to the carry-free locus `κ = 0`. -/
def carryZeroTempSupportMass {α : Type*} [Fintype α] [DecidableEq α]
    (κ : α → ℕ) (μ : α → ℝ) : ℝ :=
  (Finset.univ.filter fun a => κ a = 0).sum μ

/-- The Parry measure on a singleton carry-free essential component is the Dirac mass at its
distinguished state. -/
def carryFreeParryMeasure {α : Type*} [DecidableEq α] (root : α) : α → ℝ :=
  fun a => if a = root then 1 else 0

/-- If every state carrying positive mass satisfies `κ = 0`, then the carry-free support already
captures the whole mass of the zero-temperature limit. If there is a unique carry-free essential
state, the limiting measure is the corresponding Parry/Dirac measure.
    thm:conclusion-carry-zero-temp-support-collapse -/
theorem paper_conclusion_carry_zero_temp_support_collapse
    {α : Type*} [Fintype α] [DecidableEq α]
    (κ : α → ℕ) (μ0 : α → ℝ) (root : α)
    (hprob : ∑ a, μ0 a = 1)
    (hmax : ∀ a, μ0 a ≠ 0 → κ a = 0)
    (huniq : ∀ a, κ a = 0 → a = root) :
    carryZeroTempSupportMass κ μ0 = 1 ∧
      μ0 = carryFreeParryMeasure root := by
  have hcollapse :
      carryZeroTempSupportMass κ μ0 = ∑ a, μ0 a := by
    unfold carryZeroTempSupportMass
    calc
      (Finset.univ.filter fun a => κ a = 0).sum μ0 = ∑ a, if κ a = 0 then μ0 a else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ a, μ0 a := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        by_cases hk : κ a = 0
        · simp [hk]
        · have hμ : μ0 a = 0 := by
            by_contra hne
            exact hk (hmax a hne)
          simp [hk, hμ]
  have hother : ∀ a, a ≠ root → μ0 a = 0 := by
    intro a ha
    by_cases hk : κ a = 0
    · exact False.elim (ha (huniq a hk))
    · by_contra hμ
      exact hk (hmax a hμ)
  have hsum_root : (∑ a, μ0 a) = μ0 root := by
    rw [Finset.sum_eq_single root]
    · intro a _ ha
      exact hother a ha
    · intro hroot
      simpa using hroot
  have hroot_mass : μ0 root = 1 := by
    calc
      μ0 root = ∑ a, μ0 a := hsum_root.symm
      _ = 1 := hprob
  refine ⟨?_, ?_⟩
  · calc
      carryZeroTempSupportMass κ μ0 = ∑ a, μ0 a := hcollapse
      _ = 1 := hprob
  · funext a
    by_cases ha : a = root
    · subst ha
      simp [carryFreeParryMeasure, hroot_mass]
    · simp [carryFreeParryMeasure, ha, hother a ha]

end Omega.Conclusion
