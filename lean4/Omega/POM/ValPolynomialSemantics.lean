import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace Omega.POM

open MvPolynomial

noncomputable section

/-- Coordinate polynomials in `n` value variables with natural coefficients. -/
abbrev ValPolynomial (n : Nat) := MvPolynomial (Fin n) ℕ

/-- Coordinatewise polynomial maps on the value layer. -/
abbrev ValPolynomialMap (n : Nat) := Fin n → ValPolynomial n

/-- Primitive value-layer instructions. `EVOLVE` carries a coordinatewise polynomial map,
`PROJ_NORM` is semantically neutral, and `CLEAN` keeps a chosen set of coordinates while
resetting the rest to constants. -/
inductive ValInstruction (n : Nat) where
  | evolve (φ : ValPolynomialMap n)
  | projNorm
  | clean (keep : Finset (Fin n)) (default : Fin n → ℕ)

/-- Length-indexed value-layer words. -/
inductive ValWord (n : Nat) : Nat → Type where
  | nil : ValWord n 0
  | cons {k : Nat} : ValInstruction n → ValWord n k → ValWord n (k + 1)

namespace ValPolynomialMap

/-- Identity coordinate map. -/
def id (n : Nat) : ValPolynomialMap n := fun i => X i

/-- Coordinatewise composition by substitution. -/
def comp {n : Nat} (φ ψ : ValPolynomialMap n) : ValPolynomialMap n :=
  fun i => MvPolynomial.eval₂Hom MvPolynomial.C ψ (φ i)

/-- `CLEAN` keeps the chosen coordinates as variables and resets the others to constants. -/
def clean {n : Nat} (keep : Finset (Fin n)) (default : Fin n → ℕ) : ValPolynomialMap n :=
  fun i => if i ∈ keep then X i else C (default i)

@[simp] theorem id_apply {n : Nat} (i : Fin n) : id n i = X i := rfl

@[simp] theorem comp_apply {n : Nat} (φ ψ : ValPolynomialMap n) (i : Fin n) :
    comp φ ψ i = MvPolynomial.eval₂Hom MvPolynomial.C ψ (φ i) :=
  rfl

theorem comp_id {n : Nat} (φ : ValPolynomialMap n) : comp (id n) φ = φ := by
  funext i
  simp [comp, id]

theorem clean_apply_keep {n : Nat} {keep : Finset (Fin n)} {default : Fin n → ℕ} {i : Fin n}
    (hi : i ∈ keep) : clean keep default i = X i := by
  simp [clean, hi]

theorem clean_apply_drop {n : Nat} {keep : Finset (Fin n)} {default : Fin n → ℕ} {i : Fin n}
    (hi : i ∉ keep) : clean keep default i = C (default i) := by
  simp [clean, hi]

end ValPolynomialMap

/-- The polynomial action of a single instruction. -/
def instructionPolynomialMap {n : Nat} : ValInstruction n → ValPolynomialMap n
  | .evolve φ => φ
  | .projNorm => ValPolynomialMap.id n
  | .clean keep default => ValPolynomialMap.clean keep default

/-- The recursive polynomial semantics of a value-layer word. -/
def wordPolynomialMap {n k : Nat} : ValWord n k → ValPolynomialMap n
  | .nil => ValPolynomialMap.id n
  | .cons instr w =>
      ValPolynomialMap.comp (instructionPolynomialMap instr) (wordPolynomialMap w)

@[simp] theorem wordPolynomialMap_nil {n : Nat} :
    wordPolynomialMap (ValWord.nil (n := n)) = ValPolynomialMap.id n :=
  rfl

@[simp] theorem wordPolynomialMap_cons {n k : Nat} (instr : ValInstruction n) (w : ValWord n k) :
    wordPolynomialMap (ValWord.cons instr w) =
      ValPolynomialMap.comp (instructionPolynomialMap instr) (wordPolynomialMap w) :=
  rfl

/-- `PROJ_NORM` is neutral on the value-layer polynomial semantics. -/
theorem projNorm_neutral {n : Nat} (φ : ValPolynomialMap n) :
    ValPolynomialMap.comp (instructionPolynomialMap (.projNorm : ValInstruction n)) φ = φ := by
  simpa [instructionPolynomialMap] using ValPolynomialMap.comp_id φ

/-- `CLEAN` acts by projection on kept coordinates and constant assignment elsewhere. -/
theorem clean_coordinate_formula {n : Nat} (keep : Finset (Fin n)) (default : Fin n → ℕ)
    (i : Fin n) :
    instructionPolynomialMap (.clean keep default : ValInstruction n) i =
      if i ∈ keep then X i else C (default i) := by
  simp [instructionPolynomialMap, ValPolynomialMap.clean]

/-- A value-layer word has polynomial semantics if it is realized by some coordinatewise
`ℕ`-coefficient polynomial map. -/
def ValPolynomialSemantics {n k : Nat} (w : ValWord n k) : Prop :=
  ∃ φ : ValPolynomialMap n, wordPolynomialMap w = φ

/-- Every value-layer word denotes a coordinatewise `ℕ`-coefficient polynomial map: `EVOLVE`
supplies one step of the map, `PROJ_NORM` is neutral, `CLEAN` is projection plus constants, and
the recursive semantics closes under composition.
    thm:pom-val-polynomial-semantics -/
theorem paper_pom_val_polynomial_semantics {n k : Nat} (w : ValWord n k) :
    ValPolynomialSemantics w := by
  induction w with
  | nil =>
      exact ⟨ValPolynomialMap.id n, rfl⟩
  | @cons k instr w ih =>
      rcases ih with ⟨φ, hφ⟩
      cases instr with
      | evolve ψ =>
          exact ⟨ValPolynomialMap.comp ψ φ, by simp [wordPolynomialMap, instructionPolynomialMap, hφ]⟩
      | projNorm =>
          refine ⟨φ, ?_⟩
          simp [wordPolynomialMap, hφ, projNorm_neutral]
      | clean keep default =>
          exact
            ⟨ValPolynomialMap.comp (ValPolynomialMap.clean keep default) φ, by
              simp [wordPolynomialMap, instructionPolynomialMap, hφ]⟩

end

end Omega.POM
