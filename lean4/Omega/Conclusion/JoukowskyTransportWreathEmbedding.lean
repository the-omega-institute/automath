import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- The positive quadratic lift of a transported root `w`. -/
def conclusion_joukowsky_transport_wreath_embedding_liftPlus (w : ℝ) : ℝ :=
  (w + Real.sqrt (w ^ 2 - 4)) / 2

/-- The negative quadratic lift of a transported root `w`. -/
def conclusion_joukowsky_transport_wreath_embedding_liftMinus (w : ℝ) : ℝ :=
  (w - Real.sqrt (w ^ 2 - 4)) / 2

/-- The concrete Boolean/permutation model of the wreath product on `n` transported roots. -/
abbrev conclusion_joukowsky_transport_wreath_embedding_wreathData (n : ℕ) :=
  (Fin n → Bool) × Equiv.Perm (Fin n)

/-- The tagged lifted family obtained from a sign choice and a permutation of the transported
roots. The first coordinate keeps track of the transported root, and the second coordinate chooses
one of its two quadratic lifts. -/
def conclusion_joukowsky_transport_wreath_embedding_liftedFamily
    {n : ℕ} (w : Fin n → ℝ) :
    conclusion_joukowsky_transport_wreath_embedding_wreathData n → (Fin n → ℝ × ℝ)
  | (ε, π) => fun i =>
      let wi := w (π i)
      (wi,
        if ε i then
          conclusion_joukowsky_transport_wreath_embedding_liftPlus wi
        else
          conclusion_joukowsky_transport_wreath_embedding_liftMinus wi)

lemma conclusion_joukowsky_transport_wreath_embedding_lift_sum (w : ℝ) :
    conclusion_joukowsky_transport_wreath_embedding_liftPlus w +
        conclusion_joukowsky_transport_wreath_embedding_liftMinus w =
      w := by
  unfold conclusion_joukowsky_transport_wreath_embedding_liftPlus
    conclusion_joukowsky_transport_wreath_embedding_liftMinus
  ring

lemma conclusion_joukowsky_transport_wreath_embedding_lift_product {w : ℝ} (hw : 2 ≤ w) :
    conclusion_joukowsky_transport_wreath_embedding_liftPlus w *
        conclusion_joukowsky_transport_wreath_embedding_liftMinus w =
      1 := by
  have hnonneg : 0 ≤ w ^ 2 - 4 := by
    nlinarith
  unfold conclusion_joukowsky_transport_wreath_embedding_liftPlus
    conclusion_joukowsky_transport_wreath_embedding_liftMinus
  nlinarith [Real.sq_sqrt hnonneg]

lemma conclusion_joukowsky_transport_wreath_embedding_liftPlus_ne_liftMinus
    {w : ℝ} (hw : 2 < w) :
    conclusion_joukowsky_transport_wreath_embedding_liftPlus w ≠
      conclusion_joukowsky_transport_wreath_embedding_liftMinus w := by
  intro h
  have hdisc_pos : 0 < w ^ 2 - 4 := by
    nlinarith
  have hsqrt_pos : 0 < Real.sqrt (w ^ 2 - 4) := Real.sqrt_pos.mpr hdisc_pos
  unfold conclusion_joukowsky_transport_wreath_embedding_liftPlus
    conclusion_joukowsky_transport_wreath_embedding_liftMinus at h
  have hsqrt_zero : Real.sqrt (w ^ 2 - 4) = 0 := by
    linarith
  linarith

lemma conclusion_joukowsky_transport_wreath_embedding_liftPlus_root {w : ℝ} (hw : 2 ≤ w) :
    conclusion_joukowsky_transport_wreath_embedding_liftPlus w ^ 2 -
        w * conclusion_joukowsky_transport_wreath_embedding_liftPlus w +
        1 =
      0 := by
  have hsum := conclusion_joukowsky_transport_wreath_embedding_lift_sum w
  have hprod := conclusion_joukowsky_transport_wreath_embedding_lift_product hw
  calc
    conclusion_joukowsky_transport_wreath_embedding_liftPlus w ^ 2 -
        w * conclusion_joukowsky_transport_wreath_embedding_liftPlus w +
        1 =
      conclusion_joukowsky_transport_wreath_embedding_liftPlus w ^ 2 -
        (conclusion_joukowsky_transport_wreath_embedding_liftPlus w +
            conclusion_joukowsky_transport_wreath_embedding_liftMinus w) *
          conclusion_joukowsky_transport_wreath_embedding_liftPlus w +
        conclusion_joukowsky_transport_wreath_embedding_liftPlus w *
          conclusion_joukowsky_transport_wreath_embedding_liftMinus w := by
        rw [hsum, hprod]
    _ = 0 := by
        ring

lemma conclusion_joukowsky_transport_wreath_embedding_liftMinus_root {w : ℝ} (hw : 2 ≤ w) :
    conclusion_joukowsky_transport_wreath_embedding_liftMinus w ^ 2 -
        w * conclusion_joukowsky_transport_wreath_embedding_liftMinus w +
        1 =
      0 := by
  have hsum := conclusion_joukowsky_transport_wreath_embedding_lift_sum w
  have hprod := conclusion_joukowsky_transport_wreath_embedding_lift_product hw
  calc
    conclusion_joukowsky_transport_wreath_embedding_liftMinus w ^ 2 -
        w * conclusion_joukowsky_transport_wreath_embedding_liftMinus w +
        1 =
      conclusion_joukowsky_transport_wreath_embedding_liftMinus w ^ 2 -
        (conclusion_joukowsky_transport_wreath_embedding_liftPlus w +
            conclusion_joukowsky_transport_wreath_embedding_liftMinus w) *
          conclusion_joukowsky_transport_wreath_embedding_liftMinus w +
        conclusion_joukowsky_transport_wreath_embedding_liftPlus w *
          conclusion_joukowsky_transport_wreath_embedding_liftMinus w := by
        rw [hsum, hprod]
    _ = 0 := by
        ring

/-- Paper label: `thm:conclusion-joukowsky-transport-wreath-embedding`. The concrete Lean
surrogate solves each transported quadratic explicitly, packages the sign/permutation action on the
lifted roots, and records the cardinality of the resulting wreath-product model. -/
theorem paper_conclusion_joukowsky_transport_wreath_embedding
    {n : ℕ} (w : Fin n → ℝ) (hw_inj : Function.Injective w) (hw_gt : ∀ i, 2 < w i) :
    (∀ i,
      conclusion_joukowsky_transport_wreath_embedding_liftPlus (w i) ^ 2 -
          w i * conclusion_joukowsky_transport_wreath_embedding_liftPlus (w i) +
          1 =
        0 ∧
        conclusion_joukowsky_transport_wreath_embedding_liftMinus (w i) ^ 2 -
            w i * conclusion_joukowsky_transport_wreath_embedding_liftMinus (w i) +
            1 =
          0) ∧
      Function.Injective
        (conclusion_joukowsky_transport_wreath_embedding_liftedFamily w) ∧
      Fintype.card (conclusion_joukowsky_transport_wreath_embedding_wreathData n) =
        2 ^ n * Nat.factorial n := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨conclusion_joukowsky_transport_wreath_embedding_liftPlus_root (le_of_lt (hw_gt i)),
      conclusion_joukowsky_transport_wreath_embedding_liftMinus_root (le_of_lt (hw_gt i))⟩
  · rintro ⟨ε₁, π₁⟩ ⟨ε₂, π₂⟩ hfamily
    have hpi : π₁ = π₂ := by
      ext i
      have hpair := congrFun hfamily i
      have hfst : w (π₁ i) = w (π₂ i) := by
        simpa [conclusion_joukowsky_transport_wreath_embedding_liftedFamily] using
          congrArg Prod.fst hpair
      exact congrArg Fin.val (hw_inj hfst)
    have hε : ε₁ = ε₂ := by
      ext i
      have hpair := congrFun hfamily i
      have hsnd :
          (if ε₁ i then
              conclusion_joukowsky_transport_wreath_embedding_liftPlus (w (π₁ i))
            else
              conclusion_joukowsky_transport_wreath_embedding_liftMinus (w (π₁ i))) =
            (if ε₂ i then
                conclusion_joukowsky_transport_wreath_embedding_liftPlus (w (π₂ i))
              else
                conclusion_joukowsky_transport_wreath_embedding_liftMinus (w (π₂ i))) := by
        simpa [conclusion_joukowsky_transport_wreath_embedding_liftedFamily] using
          congrArg Prod.snd hpair
      have hsnd' :
          (if ε₁ i then
              conclusion_joukowsky_transport_wreath_embedding_liftPlus (w (π₁ i))
            else
              conclusion_joukowsky_transport_wreath_embedding_liftMinus (w (π₁ i))) =
            (if ε₂ i then
                conclusion_joukowsky_transport_wreath_embedding_liftPlus (w (π₁ i))
              else
                conclusion_joukowsky_transport_wreath_embedding_liftMinus (w (π₁ i))) := by
        simpa [hpi] using hsnd
      by_cases hε₁ : ε₁ i
      · by_cases hε₂ : ε₂ i
        · simp [hε₁, hε₂]
        · exfalso
          simp [hε₁, hε₂] at hsnd'
          exact
            conclusion_joukowsky_transport_wreath_embedding_liftPlus_ne_liftMinus
              (hw_gt (π₁ i)) hsnd'
      · by_cases hε₂ : ε₂ i
        · exfalso
          simp [hε₁, hε₂] at hsnd'
          exact
            conclusion_joukowsky_transport_wreath_embedding_liftPlus_ne_liftMinus
              (hw_gt (π₁ i)) hsnd'.symm
        · simp [hε₁, hε₂]
    simp [hε, hpi]
  · change Fintype.card ((Fin n → Bool) × Equiv.Perm (Fin n)) = 2 ^ n * Nat.factorial n
    rw [Fintype.card_prod,
      Fintype.card_fun, Fintype.card_bool]
    simpa using
      (Fintype.card_perm : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial (Fintype.card (Fin n)))

end

end Omega.Conclusion
