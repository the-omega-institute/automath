import Mathlib.Data.BitVec
import Mathlib.Data.Fintype.Card
import Omega.OperatorAlgebra.NpWatataniIndexSupportCharacterization

namespace Omega.OperatorAlgebra

open FoldJonesBasicConstructionDirectsum

/-- A finite fold family with `n`-bit outputs. -/
structure foldsharp_equals_sharpp_fold_family where
  Omega : ℕ → Type
  instFintypeOmega : ∀ n, Fintype (Omega n)
  instDecidableEqOmega : ∀ n, DecidableEq (Omega n)
  fold : ∀ n, Omega n → BitVec n

attribute [instance] foldsharp_equals_sharpp_fold_family.instFintypeOmega
attribute [instance] foldsharp_equals_sharpp_fold_family.instDecidableEqOmega

/-- `BitVec n` is finite via its equivalence with `Fin (2^n)`. -/
noncomputable instance foldsharp_equals_sharpp_bitvec_fintype (n : ℕ) : Fintype (BitVec n) :=
  Fintype.ofEquiv (Fin (2 ^ n)) BitVec.equivFin.symm.toEquiv

/-- The fiber multiplicity of a fold family at an `n`-bit output. -/
def foldsharp_equals_sharpp_fold_family.fiberCount
    (F : foldsharp_equals_sharpp_fold_family) (n : ℕ) (x : BitVec n) : ℕ := by
  letI := F.instFintypeOmega n
  letI := F.instDecidableEqOmega n
  exact Fintype.card (foldFiber (F.fold n) x)

/-- A finite verifier family with `n`-bit inputs. -/
structure foldsharp_equals_sharpp_verifier_family where
  Witness : ℕ → Type
  instFintypeWitness : ∀ n, Fintype (Witness n)
  instDecidableEqWitness : ∀ n, DecidableEq (Witness n)
  verifier : ∀ n, BitVec n → Witness n → Bool

attribute [instance] foldsharp_equals_sharpp_verifier_family.instFintypeWitness
attribute [instance] foldsharp_equals_sharpp_verifier_family.instDecidableEqWitness

/-- The witness count realized by a verifier family at an `n`-bit input. -/
def foldsharp_equals_sharpp_verifier_family.witnessCount
    (V : foldsharp_equals_sharpp_verifier_family) (n : ℕ) (x : BitVec n) : ℕ := by
  letI := V.instFintypeWitness n
  letI := V.instDecidableEqWitness n
  exact verifierWitnessCount (V.verifier n) x

/-- Fold-side realization of a counting function. -/
def foldsharp_equals_sharpp_is_foldsharp (f : ∀ n, BitVec n → ℕ) : Prop :=
  ∃ F : foldsharp_equals_sharpp_fold_family, ∀ n x, F.fiberCount n x = f n x

/-- Verifier-side realization of a counting function. -/
def foldsharp_equals_sharpp_is_sharpp (f : ∀ n, BitVec n → ℕ) : Prop :=
  ∃ V : foldsharp_equals_sharpp_verifier_family, ∀ n x, V.witnessCount n x = f n x

/-- Regard a fold family as a verifier by checking whether a candidate witness lands in the target
fiber. -/
def foldsharp_equals_sharpp_fold_to_sharpp
    (F : foldsharp_equals_sharpp_fold_family) : foldsharp_equals_sharpp_verifier_family where
  Witness := F.Omega
  instFintypeWitness := F.instFintypeOmega
  instDecidableEqWitness := F.instDecidableEqOmega
  verifier := fun n x ω => decide (F.fold n ω = x)

private def foldsharp_equals_sharpp_fold_to_sharpp_equiv
    (F : foldsharp_equals_sharpp_fold_family) (n : ℕ) (x : BitVec n) :
    foldFiber (F.fold n) x ≃
      verifierWitnesses ((foldsharp_equals_sharpp_fold_to_sharpp F).verifier n) x where
  toFun ω := ⟨ω.1, by simpa [foldsharp_equals_sharpp_fold_to_sharpp] using ω.2⟩
  invFun w := ⟨w.1, by simpa [foldsharp_equals_sharpp_fold_to_sharpp] using w.2⟩
  left_inv ω := by
    rcases ω with ⟨ω, hω⟩
    rfl
  right_inv w := by
    rcases w with ⟨w, hw⟩
    rfl

/-- The verifier obtained from a fold has exactly the same counting fibers. -/
theorem foldsharp_equals_sharpp_fold_to_sharpp_count
    (F : foldsharp_equals_sharpp_fold_family) :
    ∀ n x,
      (foldsharp_equals_sharpp_fold_to_sharpp F).witnessCount n x =
        F.fiberCount n x := by
  intro n x
  letI := F.instFintypeOmega n
  letI := F.instDecidableEqOmega n
  exact Fintype.card_congr (foldsharp_equals_sharpp_fold_to_sharpp_equiv F n x).symm

/-- Realize a verifier family as the verifier fold on accepted `(input, witness)` pairs. -/
noncomputable def foldsharp_equals_sharpp_sharpp_to_fold
    (V : foldsharp_equals_sharpp_verifier_family) : foldsharp_equals_sharpp_fold_family where
  Omega := fun n => { p : BitVec n × V.Witness n // V.verifier n p.1 p.2 = true }
  instFintypeOmega := by
    intro n
    letI := V.instFintypeWitness n
    letI := V.instDecidableEqWitness n
    infer_instance
  instDecidableEqOmega := by
    intro n
    letI := V.instFintypeWitness n
    letI := V.instDecidableEqWitness n
    infer_instance
  fold := fun n => verifierFold (V.verifier n)

private def foldsharp_equals_sharpp_sharpp_to_fold_equiv
    (V : foldsharp_equals_sharpp_verifier_family) (n : ℕ) (x : BitVec n) :
    foldFiber (verifierFold (V.verifier n)) x ≃ verifierWitnesses (V.verifier n) x where
  toFun p := by
    rcases p with ⟨⟨⟨x', w⟩, hw⟩, hx⟩
    exact ⟨w, by simpa using hx ▸ hw⟩
  invFun w := ⟨⟨(x, w.1), w.2⟩, rfl⟩
  left_inv p := by
    rcases p with ⟨⟨⟨x', w⟩, hw⟩, hx⟩
    cases hx
    rfl
  right_inv w := by
    rcases w with ⟨w, hw⟩
    rfl

/-- The verifier fold on accepted pairs has the advertised witness counts as fiber multiplicities. -/
theorem foldsharp_equals_sharpp_sharpp_to_fold_count
    (V : foldsharp_equals_sharpp_verifier_family) :
    ∀ n x,
      (foldsharp_equals_sharpp_sharpp_to_fold V).fiberCount n x =
        V.witnessCount n x := by
  intro n x
  letI := V.instFintypeWitness n
  letI := V.instDecidableEqWitness n
  exact Fintype.card_congr (foldsharp_equals_sharpp_sharpp_to_fold_equiv V n x)

/-- The finite fold-counting class and the finite verifier-counting class coincide. -/
theorem foldsharp_equals_sharpp_certified :
    ∀ f : ∀ n, BitVec n → ℕ,
      foldsharp_equals_sharpp_is_foldsharp f ↔ foldsharp_equals_sharpp_is_sharpp f := by
  intro f
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨foldsharp_equals_sharpp_fold_to_sharpp F, ?_⟩
    intro n x
    rw [foldsharp_equals_sharpp_fold_to_sharpp_count]
    exact hF n x
  · rintro ⟨V, hV⟩
    refine ⟨foldsharp_equals_sharpp_sharpp_to_fold V, ?_⟩
    intro n x
    rw [foldsharp_equals_sharpp_sharpp_to_fold_count]
    exact hV n x

/-- Paper label: `thm:FOLDsharp-equals-sharpP`. -/
def paper_foldsharp_equals_sharpp : Prop := by
  exact
    ∀ f : ∀ n, BitVec n → ℕ,
      foldsharp_equals_sharpp_is_foldsharp f ↔ foldsharp_equals_sharpp_is_sharpp f

end Omega.OperatorAlgebra
