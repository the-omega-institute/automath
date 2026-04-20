import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic
import Omega.GroupUnification.GroupJGEllipsePrimeHomomorphism
import Omega.GroupUnification.GroupJGFoldSquarefreeExternalization

namespace Omega.GroupUnification

/-- The prime-register image of a squarefree fold choice set assigns exponent `1` to each chosen
fold prime coordinate. -/
noncomputable def foldSquarefreeToPrimeRegister {m : ℕ} (S : Finset (Fin m)) :
    PrimeRegisterObject :=
  Finset.sum S fun v => primeBasis (v : ℕ)

lemma groupJGPrimeNorm_primeBasis (i : ℕ) : groupJGPrimeNorm (primeBasis i) = groupJGPrime i := by
  simp [groupJGPrimeNorm, primeBasis]

lemma groupJGPrimeNorm_foldSquarefreeToPrimeRegister {m : ℕ} (S : Finset (Fin m)) :
    groupJGPrimeNorm (foldSquarefreeToPrimeRegister S) = foldSquarefreeCode S := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp [foldSquarefreeToPrimeRegister, foldSquarefreeCode, groupJGPrimeNorm]
  | @insert a S ha ih =>
      rw [foldSquarefreeToPrimeRegister, Finset.sum_insert ha, groupJGPrimeNorm_add,
        foldSquarefreeCode, Finset.prod_insert ha, groupJGPrimeNorm_primeBasis]
      simpa [foldPrime, groupJGPrime] using congrArg (fun t => groupJGPrime (a : ℕ) * t) ih

lemma groupJGEllipseAxis_foldSquarefreeToPrimeRegister {m : ℕ} (S : Finset (Fin m)) :
    groupJGEllipseAxis (foldSquarefreeToPrimeRegister S) = foldSquarefreeCode S := by
  change ((groupJGPrimeNorm (foldSquarefreeToPrimeRegister S) : ℕ) : ℝ) =
    (foldSquarefreeCode S : ℝ)
  exact_mod_cast groupJGPrimeNorm_foldSquarefreeToPrimeRegister S

/-- Replacing the squarefree fold code by its prime-register image and then taking the ellipse axis
preserves injectivity of the visible fold data.
    cor:group-jg-fold-prime-ellipse-triple -/
theorem paper_group_jg_fold_prime_ellipse_triple (m : Nat) :
    Function.Injective
      (fun omega : FoldOmega m =>
        (omega.base, omega.hidden, groupJGEllipseAxis (foldSquarefreeToPrimeRegister omega.choices))) := by
  intro ω ω' h
  rcases ω with ⟨base, hidden, choices⟩
  rcases ω' with ⟨base', hidden', choices'⟩
  have hBase : base = base' := by
    simpa using congrArg Prod.fst h
  have hTail :
      (hidden, groupJGEllipseAxis (foldSquarefreeToPrimeRegister choices)) =
        (hidden', groupJGEllipseAxis (foldSquarefreeToPrimeRegister choices')) := by
    simpa [hBase] using congrArg Prod.snd h
  have hHidden : hidden = hidden' := by
    simpa using congrArg Prod.fst hTail
  have hAxis :
      groupJGEllipseAxis (foldSquarefreeToPrimeRegister choices) =
        groupJGEllipseAxis (foldSquarefreeToPrimeRegister choices') := by
    simpa using congrArg Prod.snd hTail
  have hCode : foldSquarefreeCode choices = foldSquarefreeCode choices' := by
    apply Nat.cast_injective (R := ℝ)
    calc
      (foldSquarefreeCode choices : ℝ) =
          groupJGEllipseAxis (foldSquarefreeToPrimeRegister choices) := by
            symm
            exact groupJGEllipseAxis_foldSquarefreeToPrimeRegister choices
      _ = groupJGEllipseAxis (foldSquarefreeToPrimeRegister choices') := hAxis
      _ = (foldSquarefreeCode choices' : ℝ) :=
            groupJGEllipseAxis_foldSquarefreeToPrimeRegister choices'
  apply foldPsi_injective m
  simp [foldPsi, hBase, hHidden, hCode]

end Omega.GroupUnification
