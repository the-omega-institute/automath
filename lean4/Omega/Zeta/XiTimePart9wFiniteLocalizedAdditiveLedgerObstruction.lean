import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart62debbFiniteLocalizationAxesNoFullMultiplicativeHost

namespace Omega.Zeta

/-- The finite additive ledger with `a + b + k` nonnegative coordinates. -/
abbrev xi_time_part9w_finite_localized_additive_ledger_obstruction_nat_ledger
    (a b k : ℕ) :=
  Fin (a + b + k) →₀ ℕ

/-- The corresponding integer ledger obtained by embedding the additive coordinates into `ℤ`. -/
abbrev xi_time_part9w_finite_localized_additive_ledger_obstruction_int_ledger
    (a b k : ℕ) :=
  Fin (a + b + k) →₀ ℤ

/-- The natural additive ledger embeds coordinatewise into the integer ledger, and once all
localized plus additive directions are counted there are only `a + b + k` available axes, so the
first forbidden full multiplicative host has size `a + b + k + 1`. -/
def xi_time_part9w_finite_localized_additive_ledger_obstruction_statement : Prop :=
  ∀ a b k : ℕ,
    Nonempty
        (xi_time_part9w_finite_localized_additive_ledger_obstruction_nat_ledger a b k ↪
          xi_time_part9w_finite_localized_additive_ledger_obstruction_int_ledger a b k) ∧
      xiLocalizedAxisMinimalChannel (a + k) b = a + b + k ∧
      ¬ xiLocalizedAxisThreshold (a + b + k + 1) (a + k) b

/-- Paper label: `thm:xi-time-part9w-finite-localized-additive-ledger-obstruction`. The additive
`ℕ`-ledger embeds in the corresponding integer ledger, and the existing finite-localization
obstruction rules out a full multiplicative host with one more generator than the available
localized plus additive axes. -/
theorem paper_xi_time_part9w_finite_localized_additive_ledger_obstruction :
    xi_time_part9w_finite_localized_additive_ledger_obstruction_statement := by
  intro a b k
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_⟩
    refine
      { toFun := fun f => f.mapRange Int.ofNat (by simp)
        inj' := ?_ }
    intro f g hfg
    ext i
    have hi := congrArg (fun u => u i) hfg
    simpa using hi
  · simp [xiLocalizedAxisMinimalChannel]
    omega
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      paper_xi_time_part62debb_finite_localization_axes_no_full_multiplicative_host (a + k) b

end Omega.Zeta
