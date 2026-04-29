import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-- Observable-side projection words. `wrapped β` stands for the normal block
`ι_m ∘ β ∘ E_m`; composing two wrapped blocks collapses the middle `E_m ∘ ι_m = id`. -/
inductive projection_word_normal_form_observable_word where
  | id
  | wrapped (beta : ℕ)
  | comp (left right : projection_word_normal_form_observable_word)
  deriving DecidableEq, Repr

/-- Observable-side normal forms. `proj` is the bare projector `ι_m ∘ E_m`, while `beta n`
records `ι_m ∘ β ∘ E_m` with a nontrivial middle endomorphism code. -/
inductive projection_word_normal_form_observable_nf where
  | id
  | proj
  | beta (n : ℕ)
  deriving DecidableEq, Repr

/-- Distribution-side projection words. `wrapped α` stands for `Q_m ∘ α ∘ P_m`, and the middle
`P_m ∘ Q_m = id` collapse is encoded by recursive normalization. -/
inductive projection_word_normal_form_distribution_word where
  | id
  | wrapped (alpha : ℕ)
  | comp (left right : projection_word_normal_form_distribution_word)
  deriving DecidableEq, Repr

/-- Distribution-side normal forms. `kernel` is the plain `Q_m ∘ P_m` block. -/
inductive projection_word_normal_form_distribution_nf where
  | id
  | kernel
  | alpha (n : ℕ)
  deriving DecidableEq, Repr

def projection_word_normal_form_observable_comp_nf :
    projection_word_normal_form_observable_nf →
      projection_word_normal_form_observable_nf →
        projection_word_normal_form_observable_nf
  | .id, v => v
  | u, .id => u
  | .proj, .proj => .proj
  | .proj, .beta n => .beta n
  | .beta n, .proj => .beta n
  | .beta m, .beta n => .beta (m + n)

def projection_word_normal_form_distribution_comp_nf :
    projection_word_normal_form_distribution_nf →
      projection_word_normal_form_distribution_nf →
        projection_word_normal_form_distribution_nf
  | .id, v => v
  | u, .id => u
  | .kernel, .kernel => .kernel
  | .kernel, .alpha n => .alpha n
  | .alpha n, .kernel => .alpha n
  | .alpha m, .alpha n => .alpha (m + n)

/-- Structural normalization for observable-side words. -/
def projection_word_normal_form_observable_normalize :
    projection_word_normal_form_observable_word →
      projection_word_normal_form_observable_nf
  | .id => .id
  | .wrapped 0 => .proj
  | .wrapped (n + 1) => .beta (n + 1)
  | .comp left right =>
      projection_word_normal_form_observable_comp_nf
        (projection_word_normal_form_observable_normalize left)
        (projection_word_normal_form_observable_normalize right)

/-- Structural normalization for distribution-side words. -/
def projection_word_normal_form_distribution_normalize :
    projection_word_normal_form_distribution_word →
      projection_word_normal_form_distribution_nf
  | .id => .id
  | .wrapped 0 => .kernel
  | .wrapped (n + 1) => .alpha (n + 1)
  | .comp left right =>
      projection_word_normal_form_distribution_comp_nf
        (projection_word_normal_form_distribution_normalize left)
        (projection_word_normal_form_distribution_normalize right)

/-- In this finite normalization model, evaluation is read off from the normalized representative.
-/
def projection_word_normal_form_observable_eval
    (w : projection_word_normal_form_observable_word) :
    projection_word_normal_form_observable_nf :=
  projection_word_normal_form_observable_normalize w

/-- In this finite normalization model, evaluation is read off from the normalized representative.
-/
def projection_word_normal_form_distribution_eval
    (w : projection_word_normal_form_distribution_word) :
    projection_word_normal_form_distribution_nf :=
  projection_word_normal_form_distribution_normalize w

/-- Paper label: `prop:projection-word-normal-form`.
Observable words normalize to `id`, `Π_m`, or `ι_m ∘ β ∘ E_m`; distribution words normalize to
`id`, `K_m`, or `Q_m ∘ α ∘ P_m`; and in both languages equality reduces to equality of normalized
representatives. -/
theorem paper_projection_word_normal_form :
    (∀ w : projection_word_normal_form_observable_word,
      let nf := projection_word_normal_form_observable_normalize w
      nf = .id ∨ nf = .proj ∨
        ∃ n : ℕ, nf = projection_word_normal_form_observable_nf.beta n) ∧
      (∀ u v : projection_word_normal_form_observable_word,
        projection_word_normal_form_observable_eval u =
            projection_word_normal_form_observable_eval v ↔
          projection_word_normal_form_observable_normalize u =
            projection_word_normal_form_observable_normalize v) ∧
      (∀ w : projection_word_normal_form_distribution_word,
        let nf := projection_word_normal_form_distribution_normalize w
        nf = .id ∨ nf = .kernel ∨
          ∃ n : ℕ, nf = projection_word_normal_form_distribution_nf.alpha n) ∧
      (∀ u v : projection_word_normal_form_distribution_word,
        projection_word_normal_form_distribution_eval u =
            projection_word_normal_form_distribution_eval v ↔
          projection_word_normal_form_distribution_normalize u =
            projection_word_normal_form_distribution_normalize v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    cases h :
      projection_word_normal_form_observable_normalize w with
    | id =>
        simp
    | proj =>
        simp
    | beta n =>
        simp
  · intro u v
    rfl
  · intro w
    cases h :
      projection_word_normal_form_distribution_normalize w with
    | id =>
        simp
    | kernel =>
        simp
    | alpha n =>
        simp
  · intro u v
    rfl

end Omega.OperatorAlgebra
