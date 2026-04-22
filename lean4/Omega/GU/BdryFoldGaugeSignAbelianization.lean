import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic
import Omega.GU.BdrySymmetricGroupSignTwistedLabelD2
import Omega.GU.BdryUpliftOrientationParity

namespace Omega.GU

/-- The orientation torsor on a `d`-sheet boundary fold is the sign torsor. -/
theorem bdryFoldGauge_orientation_eq_sign (d : ℕ) :
    upliftOrientationParity d = signHom d := rfl

/-- The sign character is nontrivial on every symmetric group `S_d` with `d ≥ 2`. -/
theorem bdryFoldGauge_sign_nontrivial (d : ℕ) (hd : 2 ≤ d) :
    (Equiv.Perm.sign : Equiv.Perm (Fin d) →* ℤˣ) ≠ 1 :=
  sign_neq_triv d hd

/-- For `d ≥ 3`, every `ℤˣ`-valued character on `S_d` is trivial or the sign character. -/
theorem bdryFoldGauge_character_classification (d : ℕ) (hd : 3 ≤ d)
    (φ : Equiv.Perm (Fin d) →* ℤˣ) :
    φ = 1 ∨ φ = Equiv.Perm.sign :=
  paper_bdry_binary_jump_orientation_functor_uniqueness d hd φ

/-- Paper-facing boundary fold gauge sign/abelianization package: the orientation torsor is the
sign torsor, the sign character is already nontrivial for `d ≥ 2`, and for `d ≥ 3` it is the
unique nontrivial `ℤˣ`-valued character on `S_d`.
    prop:bdry-fold-gauge-sign-abelianization -/
def paper_bdry_fold_gauge_sign_abelianization (d : ℕ) (hd : 2 ≤ d) : Prop := by
  let _ := hd
  exact
    upliftOrientationParity d = signHom d ∧
      (Equiv.Perm.sign : Equiv.Perm (Fin d) →* ℤˣ) ≠ 1 ∧
      (3 ≤ d → ∀ φ : Equiv.Perm (Fin d) →* ℤˣ, φ = 1 ∨ φ = Equiv.Perm.sign)

theorem paper_bdry_fold_gauge_sign_abelianization_spec (d : ℕ) (hd : 2 ≤ d) :
    paper_bdry_fold_gauge_sign_abelianization d hd := by
  refine ⟨bdryFoldGauge_orientation_eq_sign d, bdryFoldGauge_sign_nontrivial d hd, ?_⟩
  intro h3 φ
  exact bdryFoldGauge_character_classification d h3 φ

theorem paper_bdry_fold_gauge_sign_abelianization_verified (d : ℕ) (hd : 2 ≤ d) :
    paper_bdry_fold_gauge_sign_abelianization d hd := by
  exact paper_bdry_fold_gauge_sign_abelianization_spec d hd

end Omega.GU
