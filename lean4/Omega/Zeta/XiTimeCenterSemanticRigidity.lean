import Mathlib

namespace Omega.Zeta

/-- A concrete central extension with a distinguished integer-valued time register. -/
abbrev xi_time_center_semantic_rigidity_extension := ℤ × ℤ

/-- The center copy used for the time register. -/
def xi_time_center_semantic_rigidity_centerEmbedding (k : ℤ) :
    xi_time_center_semantic_rigidity_extension :=
  (0, k)

/-- Semantic preservation means that an element is central exactly when its image is central. -/
def xi_time_center_semantic_rigidity_semanticPreserving
    (φ : xi_time_center_semantic_rigidity_extension ≃+
      xi_time_center_semantic_rigidity_extension) : Prop :=
  ∀ x : xi_time_center_semantic_rigidity_extension,
    x.1 = 0 ↔ (φ x).1 = 0

/-- Restriction of the ambient automorphism to the distinguished center copy. -/
def xi_time_center_semantic_rigidity_centerRestriction
    (φ : xi_time_center_semantic_rigidity_extension ≃+
      xi_time_center_semantic_rigidity_extension) :
    ℤ →+ ℤ where
  toFun k := (φ (xi_time_center_semantic_rigidity_centerEmbedding k)).2
  map_zero' := by
    change (φ 0).2 = 0
    exact congrArg Prod.snd φ.map_zero
  map_add' a b := by
    simpa [xi_time_center_semantic_rigidity_centerEmbedding] using
      congrArg Prod.snd
        (φ.map_add
          (xi_time_center_semantic_rigidity_centerEmbedding a)
          (xi_time_center_semantic_rigidity_centerEmbedding b))

private theorem xi_time_center_semantic_rigidity_centerRestriction_mul
    (φ : xi_time_center_semantic_rigidity_extension ≃+
      xi_time_center_semantic_rigidity_extension) (k : ℤ) :
    xi_time_center_semantic_rigidity_centerRestriction φ k =
      k * xi_time_center_semantic_rigidity_centerRestriction φ 1 := by
  calc
    xi_time_center_semantic_rigidity_centerRestriction φ k =
        xi_time_center_semantic_rigidity_centerRestriction φ (k • (1 : ℤ)) := by
          simp
    _ = k • xi_time_center_semantic_rigidity_centerRestriction φ 1 := by
          simpa using
            (xi_time_center_semantic_rigidity_centerRestriction φ).map_zsmul (1 : ℤ) k
    _ = k * xi_time_center_semantic_rigidity_centerRestriction φ 1 := by
          simp

/-- Paper label: `thm:xi-time-center-semantic-rigidity`. A semantic-preserving automorphism of
the concrete central extension restricts on the distinguished integer center to either the
identity or the sign involution, hence gives a group automorphism of that copy of `ℤ`. -/
theorem paper_xi_time_center_semantic_rigidity
    (φ : xi_time_center_semantic_rigidity_extension ≃+
      xi_time_center_semantic_rigidity_extension)
    (hφ : xi_time_center_semantic_rigidity_semanticPreserving φ) :
    Function.Bijective (xi_time_center_semantic_rigidity_centerRestriction φ) ∧
      ((∀ k : ℤ, xi_time_center_semantic_rigidity_centerRestriction φ k = k) ∨
        ∀ k : ℤ, xi_time_center_semantic_rigidity_centerRestriction φ k = -k) := by
  have hsurj :
      Function.Surjective (xi_time_center_semantic_rigidity_centerRestriction φ) := by
    intro z
    rcases φ.surjective (xi_time_center_semantic_rigidity_centerEmbedding z) with ⟨x, hx⟩
    rcases x with ⟨a, b⟩
    have ha0_img : (φ (a, b)).1 = 0 := by
      simpa [xi_time_center_semantic_rigidity_centerEmbedding] using congrArg Prod.fst hx
    have ha0 : a = 0 := (hφ (a, b)).mpr ha0_img
    refine ⟨b, ?_⟩
    have hab : (a, b) = xi_time_center_semantic_rigidity_centerEmbedding b := by
      simp [xi_time_center_semantic_rigidity_centerEmbedding, ha0]
    rw [hab] at hx
    simpa [xi_time_center_semantic_rigidity_centerRestriction] using congrArg Prod.snd hx
  have hclass :
      (∀ k : ℤ, xi_time_center_semantic_rigidity_centerRestriction φ k = k) ∨
        ∀ k : ℤ, xi_time_center_semantic_rigidity_centerRestriction φ k = -k := by
    rcases hsurj 1 with ⟨k, hk⟩
    have hkMul : xi_time_center_semantic_rigidity_centerRestriction φ 1 * k = 1 := by
      have hk' : k * xi_time_center_semantic_rigidity_centerRestriction φ 1 = 1 := by
        rw [xi_time_center_semantic_rigidity_centerRestriction_mul] at hk
        exact hk
      simpa [mul_comm] using hk'
    have hsign :
        xi_time_center_semantic_rigidity_centerRestriction φ 1 = 1 ∨
          xi_time_center_semantic_rigidity_centerRestriction φ 1 = -1 :=
      Int.eq_one_or_neg_one_of_mul_eq_one hkMul
    rcases hsign with hsign | hsign
    · left
      intro z
      calc
        xi_time_center_semantic_rigidity_centerRestriction φ z =
            z * xi_time_center_semantic_rigidity_centerRestriction φ 1 :=
              xi_time_center_semantic_rigidity_centerRestriction_mul φ z
        _ = z := by simp [hsign]
    · right
      intro z
      calc
        xi_time_center_semantic_rigidity_centerRestriction φ z =
            z * xi_time_center_semantic_rigidity_centerRestriction φ 1 :=
              xi_time_center_semantic_rigidity_centerRestriction_mul φ z
        _ = -z := by simp [hsign]
  have hbij : Function.Bijective (xi_time_center_semantic_rigidity_centerRestriction φ) := by
    rcases hclass with hId | hNeg
    · refine ⟨?_, ?_⟩
      · intro a b hab
        simpa [hId a, hId b] using hab
      · intro y
        exact ⟨y, hId y⟩
    · refine ⟨?_, ?_⟩
      · intro a b hab
        apply neg_injective
        simpa [hNeg a, hNeg b] using hab
      · intro y
        refine ⟨-y, ?_⟩
        simp [hNeg (-y)]
  exact ⟨hbij, hclass⟩

end Omega.Zeta
