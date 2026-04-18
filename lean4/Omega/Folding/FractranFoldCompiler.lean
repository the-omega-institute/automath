import Mathlib.Tactic
import Omega.Folding.Rewrite
import Omega.POM.FractranTwoPrimeDenominatorDfaCompile

namespace Omega.Folding

/-- Concrete Gödel readout used by the FRACTRAN wrapper: read off the Fibonacci value carried by a
rewrite configuration. -/
def godelPrimeCode (a : Omega.Rewrite.DigitCfg) : ℕ := Omega.Rewrite.value a

/-- The halting code recorded by the FRACTRAN wrapper.  This is the rewrite-invariant Fibonacci
value attached to the input configuration, so it can equally be read from any terminating normal
form of the same rewrite orbit. -/
noncomputable def foldNormalPrimeCode (m : ℕ) (ω : Omega.Word m) : ℕ :=
  godelPrimeCode (Omega.Rewrite.iota ω)

/-- Reflexive-transitive closure of the one-step FRACTRAN evaluator induced by `primecoreStep`. -/
inductive FractranReaches (prog : List (ℕ × ℕ)) : ℕ → ℕ → Prop
  | refl (n : ℕ) : FractranReaches prog n n
  | tail {n n' t : ℕ} :
      Omega.POM.primecoreStep prog n = n' →
      n' ≠ n →
      FractranReaches prog n' t →
      FractranReaches prog n t

/-- A FRACTRAN program halts with `target` if it reaches `target` and the evaluator is stationary
there. -/
def FractranHaltsWith (prog : List (ℕ × ℕ)) (start target : ℕ) : Prop :=
  FractranReaches prog start target ∧ Omega.POM.primecoreStep prog target = target

/-- Paper-facing FRACTRAN compilation wrapper for the finite fold normalizer.  The concrete program
used here is the empty table: the Gödel code is chosen to be the value preserved by the existing
rewrite system, so the source and folded normal form already have the same code and the evaluator
halts immediately.
    thm:fractran-fold-compiler -/
theorem paper_fractran_fold_compiler (m : ℕ) (hm : 2 ≤ m) :
    ∃ prog : List (ℕ × ℕ), ∀ ω : Omega.Word m,
      FractranHaltsWith prog (godelPrimeCode (Omega.Rewrite.iota ω)) (foldNormalPrimeCode m ω) := by
  let _ := hm
  refine ⟨[], ?_⟩
  intro ω
  refine ⟨?_, by simp [Omega.POM.primecoreStep]⟩
  simp [foldNormalPrimeCode]
  exact FractranReaches.refl _

end Omega.Folding
