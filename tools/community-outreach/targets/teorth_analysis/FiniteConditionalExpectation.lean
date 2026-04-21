import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! Finite conditional expectation by averaging over fibers. -/

open scoped BigOperators

namespace ProbabilityTheory

/-- Data for a finite quotient map. -/
structure FiniteConditionalExpectationData where
  Ω : Type
  X : Type
  instDecEqΩ : DecidableEq Ω
  instFintypeΩ : Fintype Ω
  instDecEqX : DecidableEq X
  instFintypeX : Fintype X
  map : Ω → X
  map_surjective : Function.Surjective map

attribute [instance] FiniteConditionalExpectationData.instDecEqΩ
attribute [instance] FiniteConditionalExpectationData.instFintypeΩ
attribute [instance] FiniteConditionalExpectationData.instDecEqX
attribute [instance] FiniteConditionalExpectationData.instFintypeX

namespace FiniteConditionalExpectationData

/-- The fiber over a quotient point. -/
def fiber (D : FiniteConditionalExpectationData) (x : D.X) : Finset D.Ω :=
  Finset.univ.filter fun a ↦ D.map a = x

/-- The cardinality of a fiber. -/
def fiberCard (D : FiniteConditionalExpectationData) (x : D.X) : ℕ :=
  (D.fiber x).card

/-- The finite conditional expectation obtained by uniformly averaging on each fiber. -/
def fiberAverage (D : FiniteConditionalExpectationData) {𝕜 : Type*} [Field 𝕜]
    (f : D.Ω → 𝕜) : D.Ω → 𝕜 :=
  fun a ↦ (∑ b ∈ D.fiber (D.map a), f b) / D.fiberCard (D.map a)

/-- The counting-measure mean on the finite sample space. -/
def finiteMean (D : FiniteConditionalExpectationData) {𝕜 : Type*} [Field 𝕜]
    (f : D.Ω → 𝕜) : 𝕜 :=
  (∑ a, f a) / (Fintype.card D.Ω : 𝕜)

/-- The unnormalized counting-measure variance on the finite sample space. -/
def finiteVariance (D : FiniteConditionalExpectationData) {𝕜 : Type*} [Field 𝕜]
    (f : D.Ω → 𝕜) : 𝕜 :=
  ∑ a, f a ^ 2 - (Fintype.card D.Ω : 𝕜) * D.finiteMean f ^ 2

/-- Functions that are constant on fibers of the quotient map. -/
def FiberInvariant (D : FiniteConditionalExpectationData) {𝕜 : Type*} (f : D.Ω → 𝕜) : Prop :=
  ∀ a b, D.map a = D.map b → f a = f b

/-- Positivity, unitality, and idempotence of the finite conditional expectation. -/
def PositiveUnitalIdempotent (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] : Prop :=
  (∀ f : D.Ω → 𝕜, (∀ a, 0 ≤ f a) → ∀ a, 0 ≤ D.fiberAverage f a) ∧
    (D.fiberAverage (fun _ ↦ (1 : 𝕜)) = fun _ ↦ (1 : 𝕜)) ∧
      (∀ f : D.Ω → 𝕜, D.fiberAverage (D.fiberAverage f) = D.fiberAverage f)

/-- The finite conditional expectation fixes the fiber-invariant subalgebra. -/
def IdentityOnInvariantSubalgebra (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] : Prop :=
  ∀ f : D.Ω → 𝕜, D.FiberInvariant f → D.fiberAverage f = f

/-- The finite conditional expectation is a bimodule map over the invariant subalgebra. -/
def BimoduleLaw (D : FiniteConditionalExpectationData) {𝕜 : Type*} [Field 𝕜] : Prop :=
  ∀ B₁ B₂ A : D.Ω → 𝕜, D.FiberInvariant B₁ → D.FiberInvariant B₂ →
    D.fiberAverage (fun a ↦ B₁ a * A a * B₂ a) =
      fun a ↦ B₁ a * D.fiberAverage A a * B₂ a

lemma mem_fiber_self (D : FiniteConditionalExpectationData) (a : D.Ω) :
    a ∈ D.fiber (D.map a) := by
  simp [fiber]

lemma fiber_nonempty (D : FiniteConditionalExpectationData) (x : D.X) :
    (D.fiber x).Nonempty := by
  rcases D.map_surjective x with ⟨a, rfl⟩
  exact ⟨a, D.mem_fiber_self a⟩

lemma fiberCard_pos (D : FiniteConditionalExpectationData) (x : D.X) : 0 < D.fiberCard x := by
  simpa [fiberCard] using D.fiber_nonempty x |>.card_pos

lemma fiberCard_ne_zero (D : FiniteConditionalExpectationData) {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (x : D.X) : (D.fiberCard x : 𝕜) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt (D.fiberCard_pos x)

lemma fiberAverage_fiberInvariant (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] (f : D.Ω → 𝕜) :
    D.FiberInvariant (D.fiberAverage f) := by
  intro a b hab
  simp only [fiberAverage, hab]

lemma sum_eq_card_mul_of_fiberInvariant (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] (f : D.Ω → 𝕜) (hf : D.FiberInvariant f) (a : D.Ω) :
    (∑ b ∈ D.fiber (D.map a), f b) = (D.fiberCard (D.map a) : 𝕜) * f a := by
  calc
    (∑ b ∈ D.fiber (D.map a), f b) =
        ∑ b ∈ D.fiber (D.map a), f a := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          exact hf b a (by simpa [fiber] using hb)
    _ = D.fiberCard (D.map a) * f a := by
      simp [fiberCard]

lemma fiberAverage_eq_self_of_fiberInvariant (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (f : D.Ω → 𝕜) (hf : D.FiberInvariant f) :
    D.fiberAverage f = f := by
  funext a
  have hsum := D.sum_eq_card_mul_of_fiberInvariant f hf a
  rw [fiberAverage, hsum]
  field_simp [D.fiberCard_ne_zero (𝕜 := 𝕜) (D.map a)]

lemma fiberAverage_nonneg (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (f : D.Ω → 𝕜)
    (hf : ∀ a, 0 ≤ f a) (a : D.Ω) : 0 ≤ D.fiberAverage f a := by
  unfold fiberAverage
  refine div_nonneg ?_ ?_
  · exact Finset.sum_nonneg fun b _ ↦ hf b
  · exact_mod_cast Nat.zero_le (D.fiberCard (D.map a))

lemma fiberAverage_one (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    D.fiberAverage (fun _ ↦ (1 : 𝕜)) = fun _ ↦ (1 : 𝕜) := by
  exact D.fiberAverage_eq_self_of_fiberInvariant (fun _ ↦ (1 : 𝕜)) (by
    intro _ _ _
    rfl)

lemma fiberAverage_idempotent (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (f : D.Ω → 𝕜) :
    D.fiberAverage (D.fiberAverage f) = D.fiberAverage f := by
  exact D.fiberAverage_eq_self_of_fiberInvariant (D.fiberAverage f) (D.fiberAverage_fiberInvariant f)

lemma fiberAverage_bimodule (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (B₁ B₂ A : D.Ω → 𝕜)
    (hB₁ : D.FiberInvariant B₁) (hB₂ : D.FiberInvariant B₂) :
    D.fiberAverage (fun a ↦ B₁ a * A a * B₂ a) =
      fun a ↦ B₁ a * D.fiberAverage A a * B₂ a := by
  funext a
  have hcard : (D.fiberCard (D.map a) : 𝕜) ≠ 0 := D.fiberCard_ne_zero (D.map a)
  have hsum :
      (∑ b ∈ D.fiber (D.map a), B₁ b * A b * B₂ b) =
        B₁ a * (∑ b ∈ D.fiber (D.map a), A b) * B₂ a := by
    calc
      (∑ b ∈ D.fiber (D.map a), B₁ b * A b * B₂ b) =
          ∑ b ∈ D.fiber (D.map a), B₁ a * A b * B₂ a := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            have hmap : D.map b = D.map a := by
              simpa [fiber] using hb
            rw [hB₁ b a hmap, hB₂ b a hmap]
      _ = (∑ b ∈ D.fiber (D.map a), B₁ a * A b) * B₂ a := by
        rw [Finset.sum_mul]
      _ = (B₁ a * ∑ b ∈ D.fiber (D.map a), A b) * B₂ a := by
        rw [Finset.mul_sum]
      _ = B₁ a * (∑ b ∈ D.fiber (D.map a), A b) * B₂ a := by
        ring
  rw [fiberAverage, hsum, fiberAverage]
  field_simp [hcard]

lemma sum_fiberwise_univ (D : FiniteConditionalExpectationData)
    {M : Type*} [AddCommMonoid M] (g : D.Ω → M) :
    (∑ x : D.X, ∑ a ∈ D.fiber x, g a) = ∑ a : D.Ω, g a := by
  simpa [fiber] using
    (Finset.sum_fiberwise_eq_sum_filter (s := Finset.univ) (t := Finset.univ)
      (g := D.map) (f := g))

lemma fiberAverage_sum_fiber (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : D.Ω → 𝕜) (x : D.X) :
    (∑ a ∈ D.fiber x, D.fiberAverage f a) = ∑ a ∈ D.fiber x, f a := by
  have hcard : (D.fiberCard x : 𝕜) ≠ 0 := D.fiberCard_ne_zero x
  calc
    (∑ a ∈ D.fiber x, D.fiberAverage f a) =
        ∑ _a ∈ D.fiber x, (∑ b ∈ D.fiber x, f b) / (D.fiberCard x : 𝕜) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hmap : D.map a = x := by
            simpa [fiber] using ha
          simp [fiberAverage, hmap]
    _ = (D.fiberCard x : 𝕜) * ((∑ b ∈ D.fiber x, f b) / D.fiberCard x) := by
      simp [fiberCard]
    _ = ∑ a ∈ D.fiber x, f a := by
      field_simp [hcard]

lemma fiberAverage_sum_eq (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : D.Ω → 𝕜) :
    (∑ a, D.fiberAverage f a) = ∑ a, f a := by
  calc
    (∑ a, D.fiberAverage f a) =
        ∑ x : D.X, ∑ a ∈ D.fiber x, D.fiberAverage f a := by
          rw [D.sum_fiberwise_univ]
    _ = ∑ x : D.X, ∑ a ∈ D.fiber x, f a := by
      refine Finset.sum_congr rfl ?_
      intro x _
      exact D.fiberAverage_sum_fiber f x
    _ = ∑ a, f a := D.sum_fiberwise_univ f

lemma finiteMean_fiberAverage (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : D.Ω → 𝕜) :
    D.finiteMean (D.fiberAverage f) = D.finiteMean f := by
  simp [finiteMean, D.fiberAverage_sum_eq f]

lemma fiberAverage_sq_sum_fiber_le (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : D.Ω → 𝕜) (x : D.X) :
    (∑ a ∈ D.fiber x, D.fiberAverage f a ^ 2) ≤ ∑ a ∈ D.fiber x, f a ^ 2 := by
  have hcard_pos : 0 < (D.fiberCard x : 𝕜) := by
    exact_mod_cast D.fiberCard_pos x
  have hcard : (D.fiberCard x : 𝕜) ≠ 0 := ne_of_gt hcard_pos
  have hsq :
      (∑ a ∈ D.fiber x, f a) ^ 2 ≤
        (D.fiberCard x : 𝕜) * ∑ a ∈ D.fiber x, f a ^ 2 := by
    simpa [fiberCard] using
      (sq_sum_le_card_mul_sum_sq (s := D.fiber x) (f := f))
  have hdiv :
      (∑ a ∈ D.fiber x, f a) ^ 2 / (D.fiberCard x : 𝕜) ≤
        ∑ a ∈ D.fiber x, f a ^ 2 := by
    exact (div_le_iff₀ hcard_pos).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsq)
  calc
    (∑ a ∈ D.fiber x, D.fiberAverage f a ^ 2) =
        (D.fiberCard x : 𝕜) *
          ((∑ b ∈ D.fiber x, f b) / (D.fiberCard x : 𝕜)) ^ 2 := by
          calc
            (∑ a ∈ D.fiber x, D.fiberAverage f a ^ 2) =
                ∑ _a ∈ D.fiber x,
                  ((∑ b ∈ D.fiber x, f b) / (D.fiberCard x : 𝕜)) ^ 2 := by
                  refine Finset.sum_congr rfl ?_
                  intro a ha
                  have hmap : D.map a = x := by
                    simpa [fiber] using ha
                  simp [fiberAverage, hmap]
            _ = (D.fiberCard x : 𝕜) *
                  ((∑ b ∈ D.fiber x, f b) / (D.fiberCard x : 𝕜)) ^ 2 := by
              simp [fiberCard]
    _ = (∑ a ∈ D.fiber x, f a) ^ 2 / (D.fiberCard x : 𝕜) := by
      field_simp [hcard]
    _ ≤ ∑ a ∈ D.fiber x, f a ^ 2 := hdiv

/-- The finite fiber average is a contraction for the counting-measure `L²` seminorm. -/
lemma fiberAverage_sq_sum_le (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : D.Ω → 𝕜) :
    (∑ a, D.fiberAverage f a ^ 2) ≤ ∑ a, f a ^ 2 := by
  calc
    (∑ a, D.fiberAverage f a ^ 2) =
        ∑ x : D.X, ∑ a ∈ D.fiber x, D.fiberAverage f a ^ 2 := by
          rw [D.sum_fiberwise_univ]
    _ ≤ ∑ x : D.X, ∑ a ∈ D.fiber x, f a ^ 2 := by
      exact Finset.sum_le_sum fun x _ ↦ D.fiberAverage_sq_sum_fiber_le f x
    _ = ∑ a, f a ^ 2 := D.sum_fiberwise_univ fun a ↦ f a ^ 2

/-- Finite fiber averaging dissipates the unnormalized counting-measure variance. -/
lemma fiberAverage_variance_le (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (f : D.Ω → 𝕜) :
    D.finiteVariance (D.fiberAverage f) ≤ D.finiteVariance f := by
  unfold finiteVariance
  rw [D.finiteMean_fiberAverage f]
  exact sub_le_sub_right (D.fiberAverage_sq_sum_le f)
    ((Fintype.card D.Ω : 𝕜) * D.finiteMean f ^ 2)

lemma fiberAverage_eq_finiteMean_of_subsingleton (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [Subsingleton D.X] (f : D.Ω → 𝕜) :
    D.fiberAverage f = fun _ ↦ D.finiteMean f := by
  funext a
  have hfiber : D.fiber (D.map a) = Finset.univ := by
    ext b
    simp [fiber, Subsingleton.elim (D.map b) (D.map a)]
  simp [fiberAverage, finiteMean, hfiber, fiberCard]

/-- If the quotient has one atom, finite fiber averaging annihilates variance. -/
lemma fiberAverage_variance_zero_singleton (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [Subsingleton D.X] (f : D.Ω → 𝕜) :
    D.finiteVariance (D.fiberAverage f) = 0 := by
  rw [D.fiberAverage_eq_finiteMean_of_subsingleton f]
  by_cases hΩ : Nonempty D.Ω
  · haveI : Nonempty D.Ω := hΩ
    have hcard : (Fintype.card D.Ω : 𝕜) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := D.Ω))
    have hmean :
        D.finiteMean (fun _ : D.Ω ↦ D.finiteMean f) = D.finiteMean f := by
      have hsum_const :
          (∑ _ : D.Ω, D.finiteMean f) =
            (Fintype.card D.Ω : 𝕜) * D.finiteMean f := by
        simp
      calc
        D.finiteMean (fun _ : D.Ω ↦ D.finiteMean f) =
            ((Fintype.card D.Ω : 𝕜) * D.finiteMean f) /
              (Fintype.card D.Ω : 𝕜) := by
              rw [finiteMean, hsum_const]
        _ = D.finiteMean f := by
          field_simp [hcard]
    unfold finiteVariance
    rw [hmean]
    simp
  · haveI : IsEmpty D.Ω := not_nonempty_iff.mp hΩ
    simp [finiteVariance]

/-- Finite fiber averaging is positive, unital, idempotent, fixes fiber-invariant functions,
and satisfies the bimodule law over fiber-invariant functions.

For a finite sample space Ω with counting measure and the sigma-algebra obtained as the
comap along D.map, Mathlib's measure-theoretic condExp is expected to coincide pointwise
with D.fiberAverage. The abstract API already supplies the corresponding almost-everywhere
laws (condExp_const in ConditionalExpectation/Basic.lean, condExp_of_aestronglyMeasurable',
condExp_condExp_of_le, and the pull-out lemmas), while this file records the concrete finite
fiber-average formula and its elementary pointwise consequences. -/
theorem finiteConditionalExpectation (D : FiniteConditionalExpectationData)
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    D.PositiveUnitalIdempotent (𝕜 := 𝕜) ∧
      D.IdentityOnInvariantSubalgebra (𝕜 := 𝕜) ∧ D.BimoduleLaw (𝕜 := 𝕜) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, D.fiberAverage_one, ?_⟩
    · intro f hf a
      exact D.fiberAverage_nonneg f hf a
    · intro f
      exact D.fiberAverage_idempotent f
  · intro f hf
    exact D.fiberAverage_eq_self_of_fiberInvariant f hf
  · intro B₁ B₂ A hB₁ hB₂
    exact D.fiberAverage_bimodule B₁ B₂ A hB₁ hB₂

end FiniteConditionalExpectationData

end ProbabilityTheory
