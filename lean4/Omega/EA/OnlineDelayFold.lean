import Omega.EA.ValInvariant
import Omega.EA.ZeckendorfTransversal

namespace Omega.EA

open Omega.Rewrite

/-- Chapter-local online-delay fold transitions: either perform one local Fibonacci rewrite step
or terminate by emitting the canonical Zeckendorf representative of the current value. -/
inductive OnlineDelayFoldTransition : DigitCfg → DigitCfg → Prop
  | rewrite {a b : DigitCfg} : Step a b → OnlineDelayFoldTransition a b
  | normalize (a : DigitCfg) : OnlineDelayFoldTransition a (R_F (valPr a))

/-- Terminal output of the chapter-local online-delay fold transducer. -/
noncomputable def onlineDelayFoldTerminal (a : DigitCfg) : DigitCfg :=
  R_F (valPr a)

/-- The terminal online-delay output already lies in the Zeckendorf transversal. -/
def onlineDelayFoldInZeckendorfTransversal (a : DigitCfg) : Prop :=
  a ∈ PrimeRegister ∧ Irreducible a

/-- Infinite fold target used by the paper-facing uniqueness comparison. -/
noncomputable def Fold_infty (a : DigitCfg) : DigitCfg :=
  NF_pr a

/-- Every online-delay fold transition preserves the Fibonacci valuation. -/
theorem onlineDelayFoldTransition_val_invariant {a b : DigitCfg}
    (h : OnlineDelayFoldTransition a b) : valPr b = valPr a := by
  rcases h with hStep | rfl
  · exact (paper_zeckendorf_val_invariant).1 _ _ (FibCongruence.step hStep)
      |> Eq.symm
  · simpa [onlineDelayFoldTerminal] using valPr_R_F (valPr a)

/-- Paper-facing online-delay fold package: each transition preserves value, the terminal output
lands in the Zeckendorf transversal, and uniqueness of irreducible descendants identifies that
terminal output with the infinite fold. -/
theorem paper_online_delay_fold (a : DigitCfg) :
    (∀ b : DigitCfg, OnlineDelayFoldTransition a b → valPr b = valPr a) ∧
      Relation.ReflTransGen Step a (onlineDelayFoldTerminal a) ∧
      onlineDelayFoldInZeckendorfTransversal (onlineDelayFoldTerminal a) ∧
      onlineDelayFoldTerminal a = Fold_infty a := by
  have hnorm := paper_prime_register_normal_form_uniqueness a
  have htransversal := paper_zeckendorf_transversal a
  have hreduce : Relation.ReflTransGen Step a (onlineDelayFoldTerminal a) := by
    simpa [onlineDelayFoldTerminal, NF_pr] using hnorm.1
  have hterminal :
      onlineDelayFoldInZeckendorfTransversal (onlineDelayFoldTerminal a) := by
    refine ⟨?_, ?_⟩
    · simpa [onlineDelayFoldTerminal] using htransversal.2.2.1
    · simpa [onlineDelayFoldTerminal] using htransversal.2.1
  have hunique : onlineDelayFoldTerminal a = Fold_infty a := by
    have hEq : onlineDelayFoldTerminal a = NF_pr a :=
      hnorm.2.2 (onlineDelayFoldTerminal a) hreduce hterminal.2
    simpa [Fold_infty] using hEq
  refine ⟨?_, hreduce, hterminal, hunique⟩
  intro b hb
  exact onlineDelayFoldTransition_val_invariant hb

end Omega.EA
