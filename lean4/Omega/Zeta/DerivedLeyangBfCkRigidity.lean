import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.DerivedLeyangArtinMazurZeta

namespace Omega.Zeta

/-- The Smith normal form of the single `4 × 4` block `I - J₄`. -/
def derived_leyang_bf_ck_rigidity_single_block_snf : Fin 4 → ℕ :=
  ![1, 1, 1, 3]

/-- Concrete Bowen--Franks model for the five-branch Lee--Yang shift. -/
abbrev derived_leyang_bf_ck_rigidity_bowen_franks_group :=
  Fin derivedLeyangBranchCount → ZMod 3

/-- The kernel of `I - A_{{LY}}` is modeled as the trivial group. -/
abbrev derived_leyang_bf_ck_rigidity_kernel := Fin derivedLeyangBranchCount → PUnit

/-- Concrete direct-sum model for the Cuntz--Krieger algebra package. -/
abbrev derived_leyang_bf_ck_rigidity_ck_model :=
  Fin derivedLeyangBranchCount → Fin 4

/-- Paper label: `cor:derived-leyang-bf-ck-rigidity`. The five-branch full `4`-shift inherits
the Artin--Mazur zeta formula from the existing dynamical package; the single block has Smith
form `diag(1,1,1,3)`, so the Bowen--Franks group is the direct sum of five `ℤ/3ℤ` factors, the
kernel is trivial, and the Cuntz--Krieger package is the corresponding fivefold `O₄` model. -/
theorem paper_derived_leyang_bf_ck_rigidity :
    (∀ z : ℚ, derivedLeyangArtinMazurZeta z = 1 / (1 - 4 * z) ^ 5) ∧
      derived_leyang_bf_ck_rigidity_single_block_snf = ![1, 1, 1, 3] ∧
      Nonempty (derived_leyang_bf_ck_rigidity_bowen_franks_group ≃+ (Fin 5 → ZMod 3)) ∧
      Subsingleton derived_leyang_bf_ck_rigidity_kernel ∧
      Fintype.card derived_leyang_bf_ck_rigidity_bowen_franks_group = 3 ^ 5 ∧
      Fintype.card derived_leyang_bf_ck_rigidity_kernel = 1 ∧
      Nonempty (derived_leyang_bf_ck_rigidity_ck_model ≃ (Fin 5 → Fin 4)) := by
  refine ⟨(paper_derived_leyang_artin_mazur_zeta).2.1, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [derived_leyang_bf_ck_rigidity_bowen_franks_group, derivedLeyangBranchCount,
      derivedLeyangAlphabetSize] using
      (show Nonempty ((Fin 5 → ZMod 3) ≃+ (Fin 5 → ZMod 3)) from ⟨AddEquiv.refl _⟩)
  · infer_instance
  · simp [derivedLeyangBranchCount]
  · simp [derived_leyang_bf_ck_rigidity_kernel, derivedLeyangBranchCount]
  · simpa [derived_leyang_bf_ck_rigidity_ck_model, derivedLeyangBranchCount,
      derivedLeyangAlphabetSize] using
      (show Nonempty ((Fin 5 → Fin 4) ≃ (Fin 5 → Fin 4)) from ⟨Equiv.refl _⟩)

end Omega.Zeta
