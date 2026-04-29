import Omega.Zeta.XiAuditedEvenMinsectorHomotopyMod6Phase

namespace Omega.Zeta

/-- Paper label:
`cor:xi-time-part55ab-audited-even-minsector-strict-homotopy-transition`. -/
theorem paper_xi_time_part55ab_audited_even_minsector_strict_homotopy_transition
    {X : Type} (m : Nat) (hm : m = 6 ∨ m = 8 ∨ m = 10 ∨ m = 12) (d : X → Nat)
    (contractible sphereLike : X → Prop) (hd : ∀ x, d x = Nat.fib (m / 2))
    (hcontractible : ∀ x, contractible x ↔ Even (d x))
    (hsphere : ∀ x, sphereLike x ↔ Odd (d x)) :
    ((m = 6 ∨ m = 12) → ∀ x, contractible x) ∧
      ((m = 8 ∨ m = 10) → ∀ x, sphereLike x) := by
  have hphase :=
    paper_xi_audited_even_minsector_homotopy_mod6_phase m hm d contractible sphereLike hd
      hcontractible hsphere
  refine ⟨?_, ?_⟩
  · intro hcase
    apply hphase.1
    rcases hcase with rfl | rfl <;> norm_num
  · intro hcase
    apply hphase.2
    rcases hcase with rfl | rfl <;> norm_num

end Omega.Zeta
