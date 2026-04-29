import Mathlib.Tactic

namespace Omega.Zeta

/-- Pointwise semantic equivalence of two natural-number slice families. -/
def xi_no_computable_slice_bound_for_semantic_equivalence_semantically_equivalent
    (F G : ℕ → ℕ) : Prop :=
  ∀ m, F m = G m

/-- Agreement on the finite slice prefix selected by a candidate bound. -/
def xi_no_computable_slice_bound_for_semantic_equivalence_finite_slice_agreement
    (B : ℕ → ℕ) (F G : ℕ → ℕ) : Prop :=
  ∀ m, m ≤ B 0 → F m = G m

/-- Abstract computability interface for a proposed uniform slice bound. -/
def xi_no_computable_slice_bound_for_semantic_equivalence_computable
    (B : ℕ → ℕ) : Prop :=
  Nonempty (∀ n, Decidable (B n = B n))

/-- A proposed sound-and-complete finite-slice checker would turn agreement up to `B 0` into
semantic equivalence of the whole slice family. -/
def xi_no_computable_slice_bound_for_semantic_equivalence_sound_complete_by_slices
    (B : ℕ → ℕ) : Prop :=
  ∀ F G : ℕ → ℕ,
    xi_no_computable_slice_bound_for_semantic_equivalence_finite_slice_agreement B F G →
      xi_no_computable_slice_bound_for_semantic_equivalence_semantically_equivalent F G

/-- Paper label: `thm:xi-no-computable-slice-bound-for-semantic-equivalence`. -/
theorem paper_xi_no_computable_slice_bound_for_semantic_equivalence :
    ¬ ∃ B : ℕ → ℕ,
      xi_no_computable_slice_bound_for_semantic_equivalence_computable B ∧
        xi_no_computable_slice_bound_for_semantic_equivalence_sound_complete_by_slices B := by
  rintro ⟨B, _hComputable, hSoundComplete⟩
  let F : ℕ → ℕ := fun _ => 0
  let G : ℕ → ℕ := fun m => if m = B 0 + 1 then 1 else 0
  have hFinite :
      xi_no_computable_slice_bound_for_semantic_equivalence_finite_slice_agreement B F G := by
    intro m hm
    have hne : m ≠ B 0 + 1 := by omega
    simp [F, G, hne]
  have hSemantic :
      xi_no_computable_slice_bound_for_semantic_equivalence_semantically_equivalent F G :=
    hSoundComplete F G hFinite
  have hAtNext := hSemantic (B 0 + 1)
  simp [F, G] at hAtNext

end Omega.Zeta
