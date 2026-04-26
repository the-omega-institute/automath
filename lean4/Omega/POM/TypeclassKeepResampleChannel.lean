import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

noncomputable section

/-- The exponential-family normalizing mass `A = ∑ₓ uₓ`. -/
def typeclassKeepResampleNormalizer {α : Type*} [Fintype α] (u : α → ℝ) : ℝ :=
  ∑ x, u x

/-- The normalized visible weights `π(x) = uₓ / A`. -/
def typeclassKeepResamplePi {α : Type*} [Fintype α] (u : α → ℝ) (x : α) : ℝ :=
  u x / typeclassKeepResampleNormalizer u

/-- The keep probability extracted from the diagonal weight `(1 + κ) uₓ`. -/
def typeclassKeepResampleKeepProb {α : Type*} [Fintype α] (u : α → ℝ) (κ : ℝ) (x : α) : ℝ :=
  ((1 + κ) * u x) / (typeclassKeepResampleNormalizer u + κ * u x)

/-- The resampling law conditioned away from the current state `x`. -/
def typeclassKeepResampleConditionedAway {α : Type*} [Fintype α]
    (u : α → ℝ) (x y : α) : ℝ :=
  typeclassKeepResamplePi u y / (1 - typeclassKeepResamplePi u x)

/-- The rowwise-normalized keep-resample channel induced by the one-parameter Gibbs weights. -/
def typeclassKeepResampleChannel {α : Type*} [Fintype α] [DecidableEq α]
    (u : α → ℝ) (κ : ℝ) (x y : α) : ℝ :=
  if y = x then
    typeclassKeepResampleKeepProb u κ x
  else
    u y / (typeclassKeepResampleNormalizer u + κ * u x)

private lemma typeclassKeepResampleDenominatorPos {α : Type*} [Fintype α] (u : α → ℝ) (κ : ℝ)
    (hu_nonneg : ∀ x, 0 ≤ u x) (hu_lt : ∀ x, u x < typeclassKeepResampleNormalizer u)
    (hκ : -1 < κ) (x : α) :
    0 < typeclassKeepResampleNormalizer u + κ * u x := by
  have hA_sub_u_pos : 0 < typeclassKeepResampleNormalizer u - u x := sub_pos.mpr (hu_lt x)
  have hscaled_nonneg : 0 ≤ (1 + κ) * u x := by
    have hκ' : 0 ≤ 1 + κ := by linarith
    exact mul_nonneg hκ' (hu_nonneg x)
  calc
    0 < (typeclassKeepResampleNormalizer u - u x) + (1 + κ) * u x := by
      linarith
    _ = typeclassKeepResampleNormalizer u + κ * u x := by ring

private lemma one_sub_typeclassKeepResampleKeepProb_eq {α : Type*} [Fintype α]
    (u : α → ℝ) (κ : ℝ) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hu_lt : ∀ x, u x < typeclassKeepResampleNormalizer u) (hκ : -1 < κ) (x : α) :
    1 - typeclassKeepResampleKeepProb u κ x =
      (typeclassKeepResampleNormalizer u - u x) /
        (typeclassKeepResampleNormalizer u + κ * u x) := by
  have hden_ne :
      typeclassKeepResampleNormalizer u + κ * u x ≠ 0 :=
    ne_of_gt (typeclassKeepResampleDenominatorPos u κ hu_nonneg hu_lt hκ x)
  unfold typeclassKeepResampleKeepProb
  field_simp [hden_ne]
  ring

private lemma typeclassKeepResampleConditionedAway_eq {α : Type*} [Fintype α]
    (u : α → ℝ) (hApos : 0 < typeclassKeepResampleNormalizer u)
    (hu_lt : ∀ x, u x < typeclassKeepResampleNormalizer u) (x y : α) :
    typeclassKeepResampleConditionedAway u x y =
      u y / (typeclassKeepResampleNormalizer u - u x) := by
  have hA_ne : typeclassKeepResampleNormalizer u ≠ 0 := ne_of_gt hApos
  have hgap_ne : typeclassKeepResampleNormalizer u - u x ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (hu_lt x))
  unfold typeclassKeepResampleConditionedAway typeclassKeepResamplePi
  field_simp [hA_ne, hgap_ne]

/-- Paper label: `thm:pom-typeclass-keep-resample-channel`.
Rowwise normalization of the Gibbs weights produces a keep probability on the diagonal, while the
off-diagonal mass factors through the law `π` conditioned away from the current state. -/
theorem paper_pom_typeclass_keep_resample_channel {α : Type*} [Fintype α] [DecidableEq α]
    (u : α → ℝ) (κ : ℝ) (hu_nonneg : ∀ x, 0 ≤ u x)
    (hApos : 0 < typeclassKeepResampleNormalizer u)
    (hu_lt : ∀ x, u x < typeclassKeepResampleNormalizer u) (hκ : -1 < κ) :
    (∀ x, 0 ≤ typeclassKeepResampleKeepProb u κ x ∧ typeclassKeepResampleKeepProb u κ x ≤ 1) ∧
      (∀ x, typeclassKeepResampleChannel u κ x x = typeclassKeepResampleKeepProb u κ x) ∧
      (∀ ⦃x y : α⦄, y ≠ x →
        typeclassKeepResampleChannel u κ x y =
          (1 - typeclassKeepResampleKeepProb u κ x) *
            typeclassKeepResampleConditionedAway u x y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hden_pos :=
      typeclassKeepResampleDenominatorPos u κ hu_nonneg hu_lt hκ x
    constructor
    · unfold typeclassKeepResampleKeepProb
      exact div_nonneg (mul_nonneg (by linarith) (hu_nonneg x)) hden_pos.le
    · unfold typeclassKeepResampleKeepProb
      rw [div_le_iff₀ hden_pos]
      have hx_le : u x ≤ typeclassKeepResampleNormalizer u := le_of_lt (hu_lt x)
      linarith
  · intro x
    simp [typeclassKeepResampleChannel]
  · intro x y hxy
    have hden_ne :
        typeclassKeepResampleNormalizer u + κ * u x ≠ 0 :=
      ne_of_gt (typeclassKeepResampleDenominatorPos u κ hu_nonneg hu_lt hκ x)
    have hgap_ne : typeclassKeepResampleNormalizer u - u x ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt (hu_lt x))
    rw [typeclassKeepResampleChannel, if_neg hxy]
    rw [one_sub_typeclassKeepResampleKeepProb_eq u κ hu_nonneg hu_lt hκ x]
    rw [typeclassKeepResampleConditionedAway_eq u hApos hu_lt x y]
    field_simp [hden_ne, hgap_ne]

end

end Omega.POM
