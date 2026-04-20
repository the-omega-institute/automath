import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Folding

/-- The folded modular semiring from the paper is modeled concretely by the residue ring modulo
`F_{m+2}`. -/
abbrev foldModulus (m : ℕ) : ℕ := Nat.fib (m + 2)

/-- Multiplication by an idempotent residue class defines a non-unital semiring endomorphism of the
folded residue model. -/
def foldScalarEndomorphism (m : ℕ) (e : ZMod (foldModulus m)) (he : e * e = e) :
    ZMod (foldModulus m) →ₙ+* ZMod (foldModulus m) where
  toFun x := x * e
  map_mul' x y := by
    calc
      (x * y) * e = x * y * (e * e) := by
        simpa [mul_assoc] using congrArg (fun t => x * y * t) he.symm
      _ = (x * e) * (y * e) := by
        simp [mul_left_comm, mul_comm]
  map_zero' := by
    simp
  map_add' x y := by
    simp [add_mul]

/-- The image of `1` under a non-unital folded semiring endomorphism is idempotent. -/
def foldEndomorphismImageOneIdempotent (m : ℕ)
    (f : ZMod (foldModulus m) →ₙ+* ZMod (foldModulus m)) : Prop :=
  f 1 * f 1 = f 1

lemma foldEndomorphismImageOneIdempotent_proof (m : ℕ)
    (f : ZMod (foldModulus m) →ₙ+* ZMod (foldModulus m)) :
    foldEndomorphismImageOneIdempotent m f := by
  simpa [foldEndomorphismImageOneIdempotent] using
    (f.map_mul (1 : ZMod (foldModulus m)) 1).symm

lemma foldScalarEndomorphism_apply_one (m : ℕ) (e : ZMod (foldModulus m)) (he : e * e = e) :
    foldScalarEndomorphism m e he 1 = e := by
  show (1 : ZMod (foldModulus m)) * e = e
  simp

lemma fold_endomorphism_eq_mul_image_one (m : ℕ)
    (f : ZMod (foldModulus m) →ₙ+* ZMod (foldModulus m)) :
    f = foldScalarEndomorphism m (f 1) (foldEndomorphismImageOneIdempotent_proof m f) := by
  ext x
  have hnat :
      ∀ n : ℕ, f (n : ZMod (foldModulus m)) = (n : ZMod (foldModulus m)) * f 1 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        calc
          f ((n + 1 : ℕ) : ZMod (foldModulus m))
              = f ((n : ZMod (foldModulus m)) + 1) := by simp
          _ = f (n : ZMod (foldModulus m)) + f 1 := by rw [map_add]
          _ = (n : ZMod (foldModulus m)) * f 1 + f 1 := by rw [ih]
          _ = ((n : ZMod (foldModulus m)) + 1) * f 1 := by rw [add_mul, one_mul]
          _ = ((n + 1 : ℕ) : ZMod (foldModulus m)) * f 1 := by simp
  have hmod : 0 < foldModulus m := by
    simpa [foldModulus] using (Nat.fib_pos.2 (Nat.succ_pos (m + 1)))
  letI : NeZero (foldModulus m) := ⟨Nat.ne_of_gt hmod⟩
  rw [← ZMod.natCast_zmod_val x]
  exact hnat x.val

/-- Concrete classification statement for folded modular semiring endomorphisms: every non-unital
semiring endomorphism of `ZMod (F_{m+2})` is multiplication by the idempotent image of `1`, and
every idempotent produces such an endomorphism. -/
def foldModSemiringEndomorphismsIdempotentClassification : Prop :=
  ∀ m : ℕ,
    (∀ f : ZMod (foldModulus m) →ₙ+* ZMod (foldModulus m),
      foldEndomorphismImageOneIdempotent m f ∧
        f = foldScalarEndomorphism m (f 1) (foldEndomorphismImageOneIdempotent_proof m f)) ∧
    (∀ e : ZMod (foldModulus m), ∀ he : e * e = e,
      foldScalarEndomorphism m e he 1 = e)

/-- Paper-facing folded modular endomorphism classification: after transport to the residue-class
model modulo `F_{m+2}`, non-unital semiring endomorphisms are exactly multiplications by
idempotents.
    thm:fold-mod-semirings-endomorphisms-idempotents -/
def paper_fold_mod_semirings_endomorphisms_idempotents : Prop :=
  foldModSemiringEndomorphismsIdempotentClassification

theorem paper_fold_mod_semirings_endomorphisms_idempotents_proof :
    paper_fold_mod_semirings_endomorphisms_idempotents := by
  intro m
  refine ⟨?_, ?_⟩
  · intro f
    exact ⟨foldEndomorphismImageOneIdempotent_proof m f, fold_endomorphism_eq_mul_image_one m f⟩
  · intro e he
    exact foldScalarEndomorphism_apply_one m e he

end Omega.Folding
