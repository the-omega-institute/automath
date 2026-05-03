import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Conclusion.Period3FiberExactMultiplicity

namespace Omega.Conclusion

open Omega.Conclusion.Period3FiberExactMultiplicity

/-- The period-`3` fiber, identified with the Boolean block-choice cube. -/
abbrev conclusion_period3_fiber_subaxis_exponential_collision_fiber (n : ℕ) :=
  Period3FiberBlockChoices n

/-- Projection to the selected block coordinates. -/
def conclusion_period3_fiber_subaxis_exponential_collision_projection (n : ℕ)
    (S : Finset (Fin n))
    (x : conclusion_period3_fiber_subaxis_exponential_collision_fiber n) :
    ({j : Fin n // j ∈ S} → Bool) :=
  fun j => x j.1

/-- Reconstruction from selected and unselected coordinate assignments. -/
def conclusion_period3_fiber_subaxis_exponential_collision_combine (n : ℕ)
    (S : Finset (Fin n)) (selected : {j : Fin n // j ∈ S} → Bool)
    (unselected : {j : Fin n // j ∈ Sᶜ} → Bool) :
    conclusion_period3_fiber_subaxis_exponential_collision_fiber n :=
  fun j => if h : j ∈ S then selected ⟨j, h⟩ else unselected ⟨j, by simp [h]⟩

/-- Splitting the Boolean period-`3` fiber into selected and unselected coordinates. -/
def conclusion_period3_fiber_subaxis_exponential_collision_split_equiv (n : ℕ)
    (S : Finset (Fin n)) :
    conclusion_period3_fiber_subaxis_exponential_collision_fiber n ≃
      (({j : Fin n // j ∈ S} → Bool) × ({j : Fin n // j ∈ Sᶜ} → Bool)) where
  toFun x := (fun j => x j.1, fun j => x j.1)
  invFun p :=
    conclusion_period3_fiber_subaxis_exponential_collision_combine n S p.1 p.2
  left_inv x := by
    funext j
    by_cases hj : j ∈ S <;>
      simp [conclusion_period3_fiber_subaxis_exponential_collision_combine, hj]
  right_inv p := by
    ext j
    · simp [conclusion_period3_fiber_subaxis_exponential_collision_combine]
    · have hj : (j : Fin n) ∉ S := by
        exact Finset.mem_compl.mp j.2
      simp [conclusion_period3_fiber_subaxis_exponential_collision_combine, hj]

/-- Exact cardinality of the selected-coordinate Boolean cube. -/
lemma conclusion_period3_fiber_subaxis_exponential_collision_selected_card (n : ℕ)
    (S : Finset (Fin n)) :
    Fintype.card ({j : Fin n // j ∈ S} → Bool) = 2 ^ S.card := by
  classical
  rw [Fintype.card_fun]
  congr
  simp

/-- Exact cardinality of the unselected-coordinate Boolean cube. -/
lemma conclusion_period3_fiber_subaxis_exponential_collision_unselected_card (n : ℕ)
    (S : Finset (Fin n)) :
    Fintype.card ({j : Fin n // j ∈ Sᶜ} → Bool) = 2 ^ (n - S.card) := by
  classical
  have hdomain : Fintype.card {j : Fin n // j ∈ Sᶜ} = n - S.card := by
    simp
  rw [Fintype.card_fun, hdomain]
  simp

/-- Each selected-coordinate fiber is equivalent to the Boolean cube on the omitted
coordinates. -/
def conclusion_period3_fiber_subaxis_exponential_collision_level_equiv (n : ℕ)
    (S : Finset (Fin n)) (u : {j : Fin n // j ∈ S} → Bool) :
    {x : conclusion_period3_fiber_subaxis_exponential_collision_fiber n //
        conclusion_period3_fiber_subaxis_exponential_collision_projection n S x = u} ≃
      ({j : Fin n // j ∈ Sᶜ} → Bool) where
  toFun x := fun j => x.1 j.1
  invFun v :=
    ⟨conclusion_period3_fiber_subaxis_exponential_collision_combine n S u v, by
      funext j
      simp [conclusion_period3_fiber_subaxis_exponential_collision_projection,
        conclusion_period3_fiber_subaxis_exponential_collision_combine]⟩
  left_inv x := by
    ext j
    by_cases hj : j ∈ S
    · have hx := congrFun x.2 ⟨j, hj⟩
      simpa [conclusion_period3_fiber_subaxis_exponential_collision_projection,
        conclusion_period3_fiber_subaxis_exponential_collision_combine, hj] using hx.symm
    · simp [conclusion_period3_fiber_subaxis_exponential_collision_combine, hj]
  right_inv v := by
    funext j
    have hj : (j : Fin n) ∉ S := by
      exact Finset.mem_compl.mp j.2
    simp [conclusion_period3_fiber_subaxis_exponential_collision_combine, hj]

/-- Concrete subaxis collision package for the period-`3` Boolean fiber. -/
def conclusion_period3_fiber_subaxis_exponential_collision_statement : Prop :=
  ∀ n (S : Finset (Fin n)),
    Function.Surjective (conclusion_period3_fiber_subaxis_exponential_collision_projection n S) ∧
      Fintype.card ({j : Fin n // j ∈ S} → Bool) = 2 ^ S.card ∧
      Fintype.card ({j : Fin n // j ∈ Sᶜ} → Bool) = 2 ^ (n - S.card) ∧
      Fintype.card (conclusion_period3_fiber_subaxis_exponential_collision_fiber n) =
        2 ^ S.card * 2 ^ (n - S.card) ∧
      (S.card < n →
        ¬ Function.Injective
          (conclusion_period3_fiber_subaxis_exponential_collision_projection n S)) ∧
      ∀ u : {j : Fin n // j ∈ S} → Bool,
        Fintype.card
            {x : conclusion_period3_fiber_subaxis_exponential_collision_fiber n //
              conclusion_period3_fiber_subaxis_exponential_collision_projection n S x = u} =
          2 ^ (n - S.card)

/-- Paper label: `prop:conclusion-period3-fiber-subaxis-exponential-collision`. -/
theorem paper_conclusion_period3_fiber_subaxis_exponential_collision :
    conclusion_period3_fiber_subaxis_exponential_collision_statement := by
  classical
  intro n S
  have hselected :=
    conclusion_period3_fiber_subaxis_exponential_collision_selected_card n S
  have hunselected :=
    conclusion_period3_fiber_subaxis_exponential_collision_unselected_card n S
  have hfiber :
      Fintype.card (conclusion_period3_fiber_subaxis_exponential_collision_fiber n) =
        2 ^ S.card * 2 ^ (n - S.card) := by
    have hle : S.card ≤ n := by
      simpa using S.card_le_univ
    calc
      Fintype.card (conclusion_period3_fiber_subaxis_exponential_collision_fiber n) = 2 ^ n := by
        simp [conclusion_period3_fiber_subaxis_exponential_collision_fiber,
          Period3FiberBlockChoices]
      _ = 2 ^ (S.card + (n - S.card)) := by
        congr 1
        omega
      _ = 2 ^ S.card * 2 ^ (n - S.card) := by
        rw [Nat.pow_add]
  refine ⟨?_, hselected, hunselected, hfiber, ?_, ?_⟩
  · intro u
    exact
      ⟨conclusion_period3_fiber_subaxis_exponential_collision_combine n S u (fun _ => false),
        by
          funext j
          simp [conclusion_period3_fiber_subaxis_exponential_collision_projection,
            conclusion_period3_fiber_subaxis_exponential_collision_combine]⟩
  · intro hproper hinj
    have hcard_le :
        Fintype.card (conclusion_period3_fiber_subaxis_exponential_collision_fiber n) ≤
          Fintype.card ({j : Fin n // j ∈ S} → Bool) :=
      Fintype.card_le_of_injective
        (conclusion_period3_fiber_subaxis_exponential_collision_projection n S) hinj
    have hpow : 2 ^ n ≤ 2 ^ S.card := by
      simpa [conclusion_period3_fiber_subaxis_exponential_collision_fiber,
        Period3FiberBlockChoices, hselected] using hcard_le
    have hnle : n ≤ S.card :=
      (Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).1 hpow
    omega
  · intro u
    calc
      Fintype.card
          {x : conclusion_period3_fiber_subaxis_exponential_collision_fiber n //
            conclusion_period3_fiber_subaxis_exponential_collision_projection n S x = u} =
          Fintype.card ({j : Fin n // j ∈ Sᶜ} → Bool) := by
        exact Fintype.card_congr
          (conclusion_period3_fiber_subaxis_exponential_collision_level_equiv n S u)
      _ = 2 ^ (n - S.card) := hunselected

end Omega.Conclusion
