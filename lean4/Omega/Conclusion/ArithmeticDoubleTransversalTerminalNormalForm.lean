import Omega.EA.OnlineDelayFold
import Omega.POM.DoubleTransversalNormalForm

namespace Omega.Conclusion

open Omega.POM.DoubleTransversalNormalForm

/-- Conclusion-level shorthand for the arithmetic value on the prime-register configuration space. -/
noncomputable abbrev Val (a : Config) : ℤ :=
  Omega.POM.DoubleTransversalNormalForm.val a

/-- Conclusion-level remainder projection. -/
noncomputable abbrev Pi_b (n : ℤ) (b : ℕ) : ℤ :=
  Omega.POM.DoubleTransversalNormalForm.symRem n b

/-- The symmetric remainder interval used by the arithmetic double-transversal normal form. -/
def InFiber_b (b : ℕ) (r : ℤ) : Prop :=
  -((b : ℤ) / 2) ≤ r ∧ r ≤ (b : ℤ) / 2

/-- The terminal normal-form package fixes the folded representative and recovers the quotient from
the remainder. -/
def existsUniqueNormalForm (a : Config) (b : ℕ) : Prop :=
  ∃! triple : Config × ℤ × ℤ,
    triple.1 = Omega.EA.Fold_infty a ∧
      triple.2.2 = Pi_b (Val a) b ∧
      triple.2.1 = (Val a - triple.2.2) / (b : ℤ) ∧
      InFiber_b b triple.2.2 ∧
      Val a = Val triple.1 ∧
      Val a = triple.2.1 * (b : ℤ) + triple.2.2

private theorem val_fold_infty (a : Config) :
    Val (Omega.EA.Fold_infty a) = Val a := by
  have hfold : Omega.EA.onlineDelayFoldTerminal a = Omega.EA.Fold_infty a :=
    (Omega.EA.paper_online_delay_fold a).2.2.2
  change ((Omega.EA.valPr (Omega.EA.Fold_infty a) : Nat) : ℤ) = (Omega.EA.valPr a : ℤ)
  calc
    ((Omega.EA.valPr (Omega.EA.Fold_infty a) : Nat) : ℤ)
        = ((Omega.EA.valPr (Omega.EA.onlineDelayFoldTerminal a) : Nat) : ℤ) := by
            rw [← hfold]
    _ = (Omega.EA.valPr a : ℤ) := by
          simp [Omega.EA.onlineDelayFoldTerminal, Omega.EA.valPr_R_F]

private theorem canonical_division_formula (n : ℤ) (b : ℕ) (hb : 0 < b) :
    n = ((n - Pi_b n b) / (b : ℤ)) * (b : ℤ) + Pi_b n b := by
  have hspec : n = symQuo n b * (b : ℤ) + Pi_b n b := by
    simpa [Pi_b] using symQuoRem_spec n b hb
  have hsub : n - Pi_b n b = symQuo n b * (b : ℤ) := by
    linarith
  have hdiv : (b : ℤ) ∣ n - Pi_b n b := by
    refine ⟨symQuo n b, ?_⟩
    simpa [mul_comm] using hsub
  have hmul : ((n - Pi_b n b) / (b : ℤ)) * (b : ℤ) = n - Pi_b n b := by
    simpa [mul_comm] using (Int.ediv_mul_cancel hdiv)
  linarith

/-- Repackaging of the POM double-transversal normal form in the conclusion namespace: the folded
state is fixed to `Fold_infty a`, the remainder is the terminal projection `Pi_b (Val a)`, and
the quotient is recovered from that remainder by exact division.
    thm:conclusion-arithmetic-double-transversal-terminal-normal-form -/
theorem paper_conclusion_arithmetic_double_transversal_terminal_normal_form
    (a : Config) (b : ℕ) (hb : 0 < b) :
    existsUniqueNormalForm a b := by
  let x : Config := Omega.EA.Fold_infty a
  let r : ℤ := Pi_b (Val a) b
  let q : ℤ := (Val a - r) / (b : ℤ)
  refine ⟨(x, q, r), ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · exact ⟨symRem_ge (Val a) b hb, symRem_le (Val a) b hb⟩
    · simpa [x] using (val_fold_infty a).symm
    · simpa [q, r] using canonical_division_formula (Val a) b hb
  · intro triple htriple
    rcases htriple with ⟨hx, hr, hq, _, _, _⟩
    rcases triple with ⟨x', q', r'⟩
    simp only at hx hr hq
    subst hx
    subst hr
    subst hq
    rfl

end Omega.Conclusion
