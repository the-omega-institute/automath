import Mathlib.Tactic

namespace Omega.GU

/-- The visible shell quartic with explicit pure and mixed coefficients. -/
def visibleQuarticShellForm (a2 a3 a4 b : Rat) (x : Rat × Rat × Rat) : Rat :=
  a2 * x.1 ^ (4 : Nat) + a3 * x.2.1 ^ (4 : Nat) + a4 * x.2.2 ^ (4 : Nat) +
    b * (x.1 ^ (2 : Nat) * x.2.1 ^ (2 : Nat) + x.1 ^ (2 : Nat) * x.2.2 ^ (2 : Nat) +
      x.2.1 ^ (2 : Nat) * x.2.2 ^ (2 : Nat))

/-- The visible quartic shell is isotropic exactly when all pure quartic coefficients agree and
the mixed coefficient is twice that common value.
    thm:window6-visible-quartic-shell-isotropization -/
theorem paper_window6_visible_quartic_shell_isotropization (a2 a3 a4 b : Rat) :
    (Exists fun c : Rat =>
      ∀ x : Rat × Rat × Rat,
        visibleQuarticShellForm a2 a3 a4 b x =
          c * ((x.1 ^ (2 : Nat) + x.2.1 ^ (2 : Nat) + x.2.2 ^ (2 : Nat)) ^ (2 : Nat))) ↔
      (Exists fun a : Rat => a2 = a ∧ a3 = a ∧ a4 = a ∧ b = 2 * a) := by
  constructor
  · rintro ⟨c, hc⟩
    have ha2 : a2 = c := by
      have h := hc ((1 : Rat), (0 : Rat), (0 : Rat))
      norm_num [visibleQuarticShellForm] at h
      exact h
    have ha3 : a3 = c := by
      have h := hc ((0 : Rat), (1 : Rat), (0 : Rat))
      norm_num [visibleQuarticShellForm] at h
      exact h
    have ha4 : a4 = c := by
      have h := hc ((0 : Rat), (0 : Rat), (1 : Rat))
      norm_num [visibleQuarticShellForm] at h
      exact h
    have hb : b = 2 * c := by
      have h := hc ((1 : Rat), (1 : Rat), (0 : Rat))
      norm_num [visibleQuarticShellForm] at h
      linarith
    exact ⟨c, ha2, ha3, ha4, hb⟩
  · rintro ⟨a, ha2, ha3, ha4, hb⟩
    subst a2
    subst a3
    subst a4
    subst b
    refine ⟨a, ?_⟩
    intro x
    dsimp [visibleQuarticShellForm]
    ring_nf

end Omega.GU
