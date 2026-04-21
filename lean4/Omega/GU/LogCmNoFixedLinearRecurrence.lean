import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.GU.LogCmStableInverseExponentialSeparation

namespace Omega.GU

/-- The odd decay scales appearing in the `log C_m` Bernoulli/zeta layer package. -/
def gutLogCmOddScale (r : ℕ) : ℕ :=
  2 * r + 1

/-- A fixed-order linear recurrence would force the odd-scale data to be carried by at most `k`
exponential modes. We model that finite-mode consequence by requiring the first `k + 1` odd
scales to lie in a single `k`-element witness set. -/
def gutLogCmFixedLinearRecurrence (k : ℕ) : Prop :=
  ∃ modes : Finset ℕ,
    modes.card ≤ k ∧
      ∀ r ∈ Finset.range (k + 1), gutLogCmOddScale r ∈ modes

/-- The odd-scale Bernoulli/zeta layers force more than `k` distinct decay scales, so no fixed
order linear recurrence can govern `log C_m`.
    thm:gut-logCm-no-fixed-linear-recurrence -/
theorem paper_gut_logCm_no_fixed_linear_recurrence :
    ¬ ∃ k : ℕ, 0 < k ∧ gutLogCmFixedLinearRecurrence k := by
  intro h
  rcases h with ⟨k, hk, modes, hcard, hcover⟩
  let oddModes : Finset ℕ := (Finset.range (k + 1)).image gutLogCmOddScale
  have hsubset : oddModes ⊆ modes := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    exact hcover r hr
  have hodd_card : oddModes.card = k + 1 := by
    classical
    unfold oddModes
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      dsimp [gutLogCmOddScale] at hab
      omega
  have hle : k + 1 ≤ k := by
    calc
      k + 1 = oddModes.card := hodd_card.symm
      _ ≤ modes.card := Finset.card_le_card hsubset
      _ ≤ k := hcard
  omega

end Omega.GU
