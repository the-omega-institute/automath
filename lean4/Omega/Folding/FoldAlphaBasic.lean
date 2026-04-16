import Mathlib.Tactic

namespace Omega.Folding

universe u

/-- Chapter-local data for the generalized Ostrowski fold. The fold is presented through its
normal-form model and the truncation maps; functoriality is reduced to the fact that both routes
compute the same truncated normal form. -/
structure FoldAlphaBasicData where
  Word : ℕ → Type u
  legal : {m : ℕ} → Word m → Prop
  canonicalWord : {m : ℕ} → Word m → Prop
  fold : {m : ℕ} → Word m → Word m
  normalForm : {m : ℕ} → Word m → Word m
  truncate : {m₁ m₂ : ℕ} → m₁ ≤ m₂ → Word m₂ → Word m₁
  lift : {m : ℕ} → Word m → Word m
  fold_eq_normalForm : ∀ {m : ℕ} (ω : Word m), fold ω = normalForm ω
  normalForm_is_canonical : ∀ {m : ℕ} (ω : Word m), legal ω → canonicalWord (normalForm ω)
  normalForm_fixed : ∀ {m : ℕ} (ω : Word m), canonicalWord ω → normalForm ω = ω
  legal_lift : ∀ {m : ℕ} (x : Word m), canonicalWord x → legal (lift x)
  lift_retract : ∀ {m : ℕ} (x : Word m), canonicalWord x → fold (lift x) = x
  truncate_normalForm :
    ∀ {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) (ω : Word m₂),
      truncate hm (normalForm ω) = normalForm (truncate hm ω)

/-- Clause (1): the fold lands in the canonical generalized Ostrowski language. -/
def FoldAlphaBasicData.canonical (h : FoldAlphaBasicData) : Prop :=
  ∀ {m : ℕ} (ω : h.Word m), h.legal ω → h.canonicalWord (h.fold ω)

/-- Clause (2): canonical words are fixed by the fold. -/
def FoldAlphaBasicData.idempotent (h : FoldAlphaBasicData) : Prop :=
  ∀ {m : ℕ} (ω : h.Word m), h.canonicalWord ω → h.fold ω = ω

/-- Clause (3): every canonical word has a legal preimage under the fold. -/
def FoldAlphaBasicData.surjective (h : FoldAlphaBasicData) : Prop :=
  ∀ {m : ℕ} (x : h.Word m), h.canonicalWord x → ∃ ω : h.Word m, h.legal ω ∧ h.fold ω = x

/-- Clause (4): truncation commutes with folding because both sides are the same truncated normal
form. -/
def FoldAlphaBasicData.functorial (h : FoldAlphaBasicData) : Prop :=
  ∀ {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) (ω : h.Word m₂),
    h.truncate hm (h.fold ω) = h.fold (h.truncate hm ω)

set_option maxHeartbeats 400000 in
/-- Paper wrapper for the basic properties of the generalized Ostrowski fold.
    prop:fold-alpha-basic -/
theorem paper_fold_alpha_basic (h : FoldAlphaBasicData) :
    h.canonical ∧ h.idempotent ∧ h.surjective ∧ h.functorial := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m ω hlegal
    rw [h.fold_eq_normalForm]
    exact h.normalForm_is_canonical ω hlegal
  · intro m ω hcanon
    rw [h.fold_eq_normalForm]
    exact h.normalForm_fixed ω hcanon
  · intro m x hcanon
    refine ⟨h.lift x, h.legal_lift x hcanon, h.lift_retract x hcanon⟩
  · intro m₁ m₂ hm ω
    rw [h.fold_eq_normalForm, h.fold_eq_normalForm]
    exact h.truncate_normalForm hm ω

end Omega.Folding
