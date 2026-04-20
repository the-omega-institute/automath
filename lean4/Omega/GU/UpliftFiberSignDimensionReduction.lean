import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
import Omega.GU.BdryFoldGaugeSignAbelianization
import Omega.GU.BdryUpliftOrientationParity

namespace Omega.GU

/-- The labeling torsor of a `d`-sheet uplift fiber. -/
abbrev UpliftLabeling (d : ℕ) := Equiv.Perm (Fin d)

/-- Quotient relation by the alternating subgroup action on the labeling torsor. -/
def orientationOrbitRel (d : ℕ) (σ τ : UpliftLabeling d) : Prop :=
  ∃ a : Equiv.Perm (Fin d), Equiv.Perm.sign a = 1 ∧ τ = σ * a

/-- The orientation torsor obtained from labelings modulo even relabelings. -/
def upliftOrientationTorsor (d : ℕ) :=
  Quotient <| ⟨orientationOrbitRel d, by
    constructor
    · intro σ
      exact ⟨1, by simp, by simp⟩
    · intro σ τ h
      rcases h with ⟨a, ha, rfl⟩
      refine ⟨a⁻¹, ?_, by simp⟩
      simpa using congrArg Inv.inv ha
    · intro σ τ υ hστ hτυ
      rcases hστ with ⟨a, ha, rfl⟩
      rcases hτυ with ⟨b, hb, rfl⟩
      refine ⟨a * b, by simp [ha, hb], by simp [mul_assoc]⟩⟩

/-- The sign-associated two-point bundle of the labeling torsor. -/
def signAssociatedFiber (d : ℕ) :=
  Quotient <| ⟨fun σ τ : UpliftLabeling d => Equiv.Perm.sign σ = Equiv.Perm.sign τ, by
    constructor
    · intro σ
      simp
    · intro σ τ hστ
      simpa [eq_comm] using hστ
    · intro σ τ υ hστ hτυ
      exact Eq.trans hστ hτυ⟩

lemma orientationOrbitRel_iff_sign (d : ℕ) (σ τ : UpliftLabeling d) :
    orientationOrbitRel d σ τ ↔ Equiv.Perm.sign σ = Equiv.Perm.sign τ := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp [ha]
  · intro hστ
    refine ⟨σ⁻¹ * τ, ?_, by simp [mul_assoc]⟩
    have hσ : Equiv.Perm.sign σ⁻¹ = Equiv.Perm.sign σ := by
      simp
    calc
      Equiv.Perm.sign (σ⁻¹ * τ) = Equiv.Perm.sign σ⁻¹ * Equiv.Perm.sign τ := by simp
      _ = Equiv.Perm.sign σ * Equiv.Perm.sign τ := by rw [hσ]
      _ = 1 := by simpa [hστ] using sign_sq_eq_one τ

/-- The orientation torsor is naturally identified with the sign-associated two-point bundle. -/
noncomputable def upliftOrientationTorsorEquivSignFiber (d : ℕ) :
    upliftOrientationTorsor d ≃ signAssociatedFiber d where
  toFun := Quotient.map' id <| by
    intro σ τ
    exact (orientationOrbitRel_iff_sign d σ τ).mp
  invFun := Quotient.map' id <| by
    intro σ τ
    exact (orientationOrbitRel_iff_sign d σ τ).mpr
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro σ
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro σ
    rfl

lemma perm_fin_two_commutative : ∀ σ τ : Equiv.Perm (Fin 2), σ * τ = τ * σ := by
  native_decide

lemma perm_fin_three_center_trivial (z : Equiv.Perm (Fin 3))
    (hz : ∀ σ : Equiv.Perm (Fin 3), z * σ = σ * z) : z = 1 := by
  have hz01 : z 1 = Equiv.swap 0 1 (z 0) := by
    simpa using congrArg (fun p => p 0) (hz (Equiv.swap 0 1))
  have hz02 : z 2 = Equiv.swap 0 2 (z 0) := by
    simpa using congrArg (fun p => p 0) (hz (Equiv.swap 0 2))
  have hz0 : z 0 = 0 := by
    have hz0vals : (z 0).1 = 0 ∨ (z 0).1 = 1 ∨ (z 0).1 = 2 := by
      omega
    rcases hz0vals with hz0val | hz0val | hz0val
    · exact Fin.ext hz0val
    · have hz0one : z 0 = 1 := Fin.ext hz0val
      have : z 2 = 1 := by simpa [hz0one] using hz02
      have hsame : z 2 = z 0 := by simpa [hz0one] using this
      cases z.injective hsame
    · have hz0two : z 0 = 2 := Fin.ext hz0val
      have : z 1 = 2 := by simpa [hz0two] using hz01
      have hsame : z 1 = z 0 := by simpa [hz0two] using this
      cases z.injective hsame
  have hz1 : z 1 = 1 := by simpa [hz0] using hz01
  have hz2 : z 2 = 2 := by
    have hz2vals : (z 2).1 = 0 ∨ (z 2).1 = 1 ∨ (z 2).1 = 2 := by
      omega
    rcases hz2vals with hz2val | hz2val | hz2val
    · have hz2zero : z 2 = 0 := Fin.ext hz2val
      have hsame : z 2 = z 0 := by simpa [hz0] using hz2zero
      cases z.injective hsame
    · have hz2one : z 2 = 1 := Fin.ext hz2val
      have hsame : z 2 = z 1 := by simpa [hz1] using hz2one
      cases z.injective hsame
    · exact Fin.ext hz2val
  ext i
  fin_cases i <;> simp [hz0, hz1, hz2]

/-- Paper package: the orientation torsor is the sign-associated two-point bundle, the two-sheet
fiber already exhibits the central flip because `S₂` is abelian, and on three sheets every
nontrivial `ℤˣ`-valued character is the sign character while the center is trivial.
    prop:uplift-fiber-sign-dimension-reduction -/
theorem paper_gu_uplift_fiber_sign_dimension_reduction :
    (∀ d : ℕ, Nonempty (upliftOrientationTorsor d ≃ signAssociatedFiber d)) ∧
      (∀ σ τ : Equiv.Perm (Fin 2), σ * τ = τ * σ) ∧
      (∀ z : Equiv.Perm (Fin 3), (∀ σ : Equiv.Perm (Fin 3), z * σ = σ * z) → z = 1) ∧
      (∀ φ : Equiv.Perm (Fin 3) →* ℤˣ, φ ≠ 1 → φ = upliftOrientationParity 3) := by
  refine ⟨fun d => ⟨upliftOrientationTorsorEquivSignFiber d⟩, ?_, ?_, ?_⟩
  · intro σ τ
    exact perm_fin_two_commutative σ τ
  · intro z hz
    exact perm_fin_three_center_trivial z hz
  · intro φ hφ
    exact upliftOrientationParity_three_unique φ hφ

end Omega.GU
