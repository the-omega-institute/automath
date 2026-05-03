import Mathlib.Tactic

namespace Omega.Conclusion

/-- The simultaneous Hankel-minor valuation equalities for one residue-field unit. -/
def conclusion_padic_hankel_global_rigidifier_goodEvent
    (κ q : ℕ) (valuation : Fin κ → Fin q → ℤ) (tropicalMinimum : Fin κ → ℤ)
    (u : Fin q) : Prop :=
  ∀ r : Fin κ, valuation r u = tropicalMinimum r

/-- Uniform probability of the simultaneous deresonance event on the finite unit model. -/
noncomputable def conclusion_padic_hankel_global_rigidifier_probability
    (κ q : ℕ) (valuation : Fin κ → Fin q → ℤ) (tropicalMinimum : Fin κ → ℤ) : ℝ :=
  by
    classical
    exact
      (Fintype.card
            {u : Fin q //
              conclusion_padic_hankel_global_rigidifier_goodEvent κ q valuation tropicalMinimum u} :
          ℝ) /
        (q : ℝ)

/-- Concrete positive-probability extraction form of the global-rigidifier corollary. If
simultaneous deresonance gives probability at least `1 - κ / q` and `q > κ`, then the good event is
nonempty, so some residue-field unit realizes every Hankel minor valuation equality. -/
def conclusion_padic_hankel_global_rigidifier_statement : Prop :=
  ∀ (κ q : ℕ) (valuation : Fin κ → Fin q → ℤ) (tropicalMinimum : Fin κ → ℤ),
    κ < q →
      1 - (κ : ℝ) / (q : ℝ) ≤
          conclusion_padic_hankel_global_rigidifier_probability κ q valuation tropicalMinimum →
        ∃ u : Fin q,
          conclusion_padic_hankel_global_rigidifier_goodEvent κ q valuation tropicalMinimum u

/-- Paper label: `cor:conclusion-padic-hankel-global-rigidifier`. Positive probability under the
simultaneous deresonance bound extracts a unit witness satisfying all Hankel-minor valuation
equalities. -/
theorem paper_conclusion_padic_hankel_global_rigidifier :
    conclusion_padic_hankel_global_rigidifier_statement := by
  classical
  intro κ q valuation tropicalMinimum hκq hprob
  have hq_pos_nat : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le κ) hκq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
  have hκq_real : (κ : ℝ) < (q : ℝ) := by exact_mod_cast hκq
  have hfrac_lt_one : (κ : ℝ) / (q : ℝ) < 1 := by
    exact (div_lt_one hq_pos).2 hκq_real
  have hlower_pos : 0 < 1 - (κ : ℝ) / (q : ℝ) := by linarith
  have hprob_pos :
      0 <
        conclusion_padic_hankel_global_rigidifier_probability κ q valuation tropicalMinimum :=
    lt_of_lt_of_le hlower_pos hprob
  let goodSubtype :=
    {u : Fin q //
      conclusion_padic_hankel_global_rigidifier_goodEvent κ q valuation tropicalMinimum u}
  have hcard_pos : 0 < Fintype.card goodSubtype := by
    by_contra hnot
    have hcard_zero : Fintype.card goodSubtype = 0 := Nat.eq_zero_of_not_pos hnot
    have hprob_zero :
        conclusion_padic_hankel_global_rigidifier_probability κ q valuation tropicalMinimum =
          0 := by
      rw [conclusion_padic_hankel_global_rigidifier_probability]
      change (Fintype.card goodSubtype : ℝ) / (q : ℝ) = 0
      rw [hcard_zero]
      simp
    linarith
  obtain ⟨u⟩ : Nonempty goodSubtype := Fintype.card_pos_iff.mp hcard_pos
  exact ⟨u.1, u.2⟩

end Omega.Conclusion
