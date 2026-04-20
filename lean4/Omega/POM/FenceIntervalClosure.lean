import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- A fence-ideal profile records one ideal coordinate for each fence component length. -/
abbrev FenceIdealProfile (lengths : List ℕ) : Type :=
  (i : Fin lengths.length) → Fin (lengths.get i + 1)

/-- The interval of fence ideals lying above a fixed base ideal `I`. -/
def FenceIdealInterval (lengths : List ℕ) (I : FenceIdealProfile lengths) : Type :=
  {K : FenceIdealProfile lengths // ∀ i, I i ≤ K i}

/-- The residual component length after removing the base ideal coordinate. -/
def restrictedFenceComponentLength (lengths : List ℕ) (I : FenceIdealProfile lengths)
    (i : Fin lengths.length) : ℕ :=
  lengths.get i - I i

/-- The induced interval object, componentwise identified with the residual fence lengths. -/
abbrev RestrictedFenceIdealObject (lengths : List ℕ) (I : FenceIdealProfile lengths) : Type :=
  (i : Fin lengths.length) → Fin (restrictedFenceComponentLength lengths I i + 1)

/-- The interval equivalence `K ↦ K \ I` with inverse `L ↦ I ∪ L`, performed componentwise on the
fence coordinates. -/
def fenceIntervalEquivRestricted (lengths : List ℕ) (I : FenceIdealProfile lengths) :
    FenceIdealInterval lengths I ≃ RestrictedFenceIdealObject lengths I where
  toFun := fun K i =>
    ⟨K.1 i - I i, by
      have hupper : (K.1 i : ℕ) < lengths.get i + 1 := (K.1 i).is_lt
      have hupper' : (K.1 i : ℕ) ≤ lengths.get i := Nat.lt_succ_iff.mp hupper
      have hsub : (K.1 i : ℕ) - I i ≤ lengths.get i - I i :=
        Nat.sub_le_sub_right hupper' (I i)
      exact Nat.lt_succ_of_le (by simpa [restrictedFenceComponentLength] using hsub)⟩
  invFun := fun L =>
    ⟨fun i =>
        ⟨I i + L i, by
          have hi : (I i : ℕ) < lengths.get i + 1 := (I i).is_lt
          have hL : (L i : ℕ) < restrictedFenceComponentLength lengths I i + 1 := (L i).is_lt
          have hi' : (I i : ℕ) ≤ lengths.get i := Nat.lt_succ_iff.mp hi
          have hL' : (L i : ℕ) ≤ restrictedFenceComponentLength lengths I i :=
            Nat.lt_succ_iff.mp hL
          have hadd : (I i : ℕ) + L i ≤ I i + restrictedFenceComponentLength lengths I i :=
            Nat.add_le_add_left hL' (I i)
          have hbound : (I i : ℕ) + L i ≤ lengths.get i := by
            calc
              (I i : ℕ) + L i ≤ I i + restrictedFenceComponentLength lengths I i := hadd
              _ = lengths.get i := Nat.add_sub_of_le hi'
          exact Nat.lt_succ_of_le hbound⟩,
      fun i => by
        exact Nat.le_add_right (I i : ℕ) (L i : ℕ)⟩
  left_inv := by
    intro K
    apply Subtype.ext
    funext i
    apply Fin.ext
    dsimp
    exact Nat.add_sub_of_le (K.2 i)
  right_inv := by
    intro L
    funext i
    apply Fin.ext
    dsimp
    exact Nat.add_sub_cancel_left (I i : ℕ) (L i : ℕ)

/-- Removing a base ideal from a fence interval gives a new fence-ideal object with residual
component lengths, and each component remains a fence of the expected shorter length.
    thm:pom-fence-interval-closure -/
theorem paper_pom_fence_interval_closure (lengths : List ℕ) (I : FenceIdealProfile lengths) :
    Nonempty (FenceIdealInterval lengths I ≃ RestrictedFenceIdealObject lengths I) ∧
      ∀ i : Fin lengths.length,
        I i + restrictedFenceComponentLength lengths I i = lengths.get i := by
  refine ⟨⟨fenceIntervalEquivRestricted lengths I⟩, ?_⟩
  intro i
  dsimp [restrictedFenceComponentLength]
  have hi : (I i : ℕ) ≤ lengths.get i := by
    have hlt : (I i : ℕ) < lengths.get i + 1 := (I i).is_lt
    omega
  exact Nat.add_sub_of_le hi

end Omega.POM
