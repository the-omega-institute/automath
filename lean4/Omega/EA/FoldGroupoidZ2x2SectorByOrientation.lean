import Mathlib.Tactic
import Omega.EA.ChiRigidityShadow
import Omega.EA.Wedderburn
import Omega.EA.Z2x2JointSpectralMeasure

namespace Omega.EA

open scoped BigOperators

/-- The sign of a permutation, encoded as a Boolean. -/
def permSignBit {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : Bool :=
  decide ((Equiv.Perm.sign σ : ℤ) = 1)

/-- The orientation tag attached to the scan/reversal permutations on a fiber block. -/
def foldOrientationTag {α : Type*} [Fintype α] [DecidableEq α]
    (c iota : Equiv.Perm α) : Z2x2Character :=
  (permSignBit c, permSignBit iota)

/-- The set of Wedderburn block indices with a fixed orientation tag. -/
noncomputable def foldOrientationSectorIndices (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (c iota : ∀ x, Equiv.Perm (F x))
    (η : Z2x2Character) : Finset (X m) :=
  Finset.univ.filter fun x => foldOrientationTag (c x) (iota x) = η

/-- The total Wedderburn weight carried by one orientation sector. -/
noncomputable def foldOrientationSectorWeight (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (c iota : ∀ x, Equiv.Perm (F x))
    (η : Z2x2Character) : ℕ :=
  ∑ x : X m, if foldOrientationTag (c x) (iota x) = η then X.fiberMultiplicity x ^ 2 else 0

/-- Conjugate a family of fiberwise permutations by a second family. -/
def foldOrientationConj (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (σ τ : ∀ x, Equiv.Perm (F x)) : ∀ x, Equiv.Perm (F x) :=
  fun x => σ x * τ x * (σ x)⁻¹

lemma permSignBit_conj_eq {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm α) :
    permSignBit (σ * τ * σ⁻¹) = permSignBit τ := by
  unfold permSignBit
  rw [sign_conj_eq_sign]

lemma foldOrientationTag_conj_eq (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (σ c iota : ∀ x, Equiv.Perm (F x)) (x : X m) :
    foldOrientationTag ((foldOrientationConj m σ c) x) ((foldOrientationConj m σ iota) x) =
      foldOrientationTag (c x) (iota x) := by
  simp [foldOrientationTag, foldOrientationConj, permSignBit_conj_eq]

lemma mem_foldOrientationSectorIndices_own (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (c iota : ∀ x, Equiv.Perm (F x)) (x : X m) :
    x ∈ foldOrientationSectorIndices m c iota (foldOrientationTag (c x) (iota x)) := by
  simp [foldOrientationSectorIndices]

lemma disjoint_foldOrientationSectorIndices (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (c iota : ∀ x, Equiv.Perm (F x)) {η₁ η₂ : Z2x2Character}
    (hη : η₁ ≠ η₂) :
    Disjoint (foldOrientationSectorIndices m c iota η₁)
      (foldOrientationSectorIndices m c iota η₂) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx₁ hx₂
  have h₁ : foldOrientationTag (c x) (iota x) = η₁ := by
    simpa [foldOrientationSectorIndices] using hx₁
  have h₂ : foldOrientationTag (c x) (iota x) = η₂ := by
    simpa [foldOrientationSectorIndices] using hx₂
  exact hη (h₁.symm.trans h₂)

lemma sum_foldOrientationSectorWeight (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (c iota : ∀ x, Equiv.Perm (F x)) :
    ∑ η : Z2x2Character, foldOrientationSectorWeight m c iota η = momentSum 2 m := by
  unfold foldOrientationSectorWeight
  rw [Finset.sum_comm]
  calc
    (∑ x : X m, ∑ η : Z2x2Character,
        if foldOrientationTag (c x) (iota x) = η then X.fiberMultiplicity x ^ 2 else 0
      ) = ∑ x : X m, X.fiberMultiplicity x ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rcases foldOrientationTag (c x) (iota x) with ⟨sx, tx⟩
        cases sx <;> cases tx <;> simp
    _ = momentSum 2 m := rfl

lemma foldOrientationSectorIndices_conj_eq (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (σ c iota : ∀ x, Equiv.Perm (F x)) (η : Z2x2Character) :
    foldOrientationSectorIndices m (foldOrientationConj m σ c) (foldOrientationConj m σ iota) η =
      foldOrientationSectorIndices m c iota η := by
  ext x
  simp [foldOrientationSectorIndices, foldOrientationTag_conj_eq]

lemma foldOrientationSectorWeight_conj_eq (m : ℕ) {F : X m → Type*} [∀ x, Fintype (F x)]
    [∀ x, DecidableEq (F x)] (σ c iota : ∀ x, Equiv.Perm (F x)) (η : Z2x2Character) :
    foldOrientationSectorWeight m (foldOrientationConj m σ c) (foldOrientationConj m σ iota) η =
      foldOrientationSectorWeight m c iota η := by
  unfold foldOrientationSectorWeight
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp [foldOrientationTag_conj_eq]

/-- Paper label: `prop:fold-groupoid-z2x2-sector-by-orientation`. The orientation signs partition
the Wedderburn blocks into four disjoint sectors, their total sector weight recovers the full
Wedderburn dimension, and blockwise permutation-matrix conjugation preserves each sector. -/
theorem paper_fold_groupoid_z2x2_sector_by_orientation (m : ℕ) {F : X m → Type*}
    [∀ x, Fintype (F x)] [∀ x, DecidableEq (F x)] (c iota : ∀ x, Equiv.Perm (F x)) :
    (∀ x, x ∈ foldOrientationSectorIndices m c iota (foldOrientationTag (c x) (iota x))) ∧
      (∀ {η₁ η₂ : Z2x2Character}, η₁ ≠ η₂ →
        Disjoint (foldOrientationSectorIndices m c iota η₁)
          (foldOrientationSectorIndices m c iota η₂)) ∧
      (∑ η : Z2x2Character, foldOrientationSectorWeight m c iota η = momentSum 2 m) ∧
      ∀ σ : ∀ x, Equiv.Perm (F x),
        (∀ η,
          foldOrientationSectorIndices m (foldOrientationConj m σ c)
            (foldOrientationConj m σ iota) η =
            foldOrientationSectorIndices m c iota η) ∧
        (∀ η,
          foldOrientationSectorWeight m (foldOrientationConj m σ c)
            (foldOrientationConj m σ iota) η =
            foldOrientationSectorWeight m c iota η) := by
  refine ⟨mem_foldOrientationSectorIndices_own m c iota,
    (fun hη => disjoint_foldOrientationSectorIndices m c iota hη),
    sum_foldOrientationSectorWeight m c iota, ?_⟩
  intro σ
  exact ⟨foldOrientationSectorIndices_conj_eq m σ c iota,
    foldOrientationSectorWeight_conj_eq m σ c iota⟩

end Omega.EA
