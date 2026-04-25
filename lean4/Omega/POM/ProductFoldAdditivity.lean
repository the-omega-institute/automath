import Mathlib

namespace Omega.POM

open scoped BigOperators

/-- Fiber multiplicities on the Cartesian-product fold. -/
def pom_product_fold_additivity_productFiber {α β : Type*} (d₁ : α → ℕ) (d₂ : β → ℕ) :
    α × β → ℕ :=
  fun ab => d₁ ab.1 * d₂ ab.2

/-- Finite `q`-collision sum attached to a multiplicity profile. -/
def pom_product_fold_additivity_collisionSum {α : Type*} [Fintype α] (q : ℕ) (d : α → ℕ) : ℕ :=
  ∑ x, d x ^ q

/-- Logarithmic collision exponent for the finite collision sum. -/
noncomputable def pom_product_fold_additivity_collisionExponent {α : Type*} [Fintype α] (q : ℕ)
    (d : α → ℕ) : ℝ :=
  Real.log (pom_product_fold_additivity_collisionSum q d : ℝ)

/-- Maximal fiber multiplicity in one finite layer. -/
def pom_product_fold_additivity_maxFiber {α : Type*} [Fintype α] (d : α → ℕ) : ℕ :=
  Finset.univ.sup d

/-- Logarithmic worst-fiber exponent. -/
noncomputable def pom_product_fold_additivity_worstExponent {α : Type*} [Fintype α]
    (d : α → ℕ) : ℝ :=
  Real.log (pom_product_fold_additivity_maxFiber d : ℝ)

lemma pom_product_fold_additivity_collisionSum_product {α β : Type*} [Fintype α] [Fintype β]
    (q : ℕ) (d₁ : α → ℕ) (d₂ : β → ℕ) :
    pom_product_fold_additivity_collisionSum q
        (pom_product_fold_additivity_productFiber d₁ d₂) =
      pom_product_fold_additivity_collisionSum q d₁ *
        pom_product_fold_additivity_collisionSum q d₂ := by
  classical
  unfold pom_product_fold_additivity_collisionSum pom_product_fold_additivity_productFiber
  rw [Fintype.sum_prod_type]
  calc
    ∑ a, ∑ b, (d₁ a * d₂ b) ^ q = ∑ a, ∑ b, d₁ a ^ q * d₂ b ^ q := by
      refine Finset.sum_congr rfl ?_
      intro a _
      refine Finset.sum_congr rfl ?_
      intro b _
      rw [Nat.mul_pow]
    _ = ∑ a, d₁ a ^ q * ∑ b, d₂ b ^ q := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [Finset.mul_sum]
    _ = (∑ a, d₁ a ^ q) * ∑ b, d₂ b ^ q := by
      rw [← Finset.sum_mul]

lemma pom_product_fold_additivity_collisionSum_pos {α : Type*} [Fintype α] [Nonempty α] (q : ℕ)
    [NeZero q] (d : α → ℕ) (a : α) (ha : 0 < d a) :
    0 < pom_product_fold_additivity_collisionSum q d := by
  unfold pom_product_fold_additivity_collisionSum
  have hterm : 0 < d a ^ q := Nat.pow_pos ha
  have hle : d a ^ q ≤ ∑ x, d x ^ q := by
    simpa using
      (Finset.single_le_sum (f := fun x : α => d x ^ q) (fun x _ => Nat.zero_le _)
        (by simp : a ∈ (Finset.univ : Finset α)))
  exact lt_of_lt_of_le hterm hle

lemma pom_product_fold_additivity_maxFiber_product {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (d₁ : α → ℕ) (d₂ : β → ℕ) :
    pom_product_fold_additivity_maxFiber (pom_product_fold_additivity_productFiber d₁ d₂) =
      pom_product_fold_additivity_maxFiber d₁ * pom_product_fold_additivity_maxFiber d₂ := by
  classical
  unfold pom_product_fold_additivity_maxFiber pom_product_fold_additivity_productFiber
  have hle :
      Finset.univ.sup (fun ab : α × β => d₁ ab.1 * d₂ ab.2) ≤
        Finset.univ.sup d₁ * Finset.univ.sup d₂ := by
    refine Finset.sup_le ?_
    intro ab _
    exact Nat.mul_le_mul
      (Finset.le_sup (s := (Finset.univ : Finset α)) (f := d₁) (by simp))
      (Finset.le_sup (s := (Finset.univ : Finset β)) (f := d₂) (by simp))
  obtain ⟨a₀, -, ha₀⟩ :=
    Finset.exists_mem_eq_sup (s := (Finset.univ : Finset α)) Finset.univ_nonempty d₁
  obtain ⟨b₀, -, hb₀⟩ :=
    Finset.exists_mem_eq_sup (s := (Finset.univ : Finset β)) Finset.univ_nonempty d₂
  have hge :
      Finset.univ.sup d₁ * Finset.univ.sup d₂ ≤
        Finset.univ.sup (fun ab : α × β => d₁ ab.1 * d₂ ab.2) := by
    have hpair :
        d₁ a₀ * d₂ b₀ ≤ Finset.univ.sup (fun ab : α × β => d₁ ab.1 * d₂ ab.2) := by
      exact Finset.le_sup
        (s := (Finset.univ : Finset (α × β))) (f := fun ab : α × β => d₁ ab.1 * d₂ ab.2)
        (b := (a₀, b₀)) (by simp)
    simpa [ha₀, hb₀] using hpair
  exact le_antisymm hle hge

lemma pom_product_fold_additivity_collisionExponent_add {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (q : ℕ) [NeZero q] (d₁ : α → ℕ) (d₂ : β → ℕ) (a : α) (b : β)
    (ha : 0 < d₁ a) (hb : 0 < d₂ b) :
    pom_product_fold_additivity_collisionExponent q
        (pom_product_fold_additivity_productFiber d₁ d₂) =
      pom_product_fold_additivity_collisionExponent q d₁ +
        pom_product_fold_additivity_collisionExponent q d₂ := by
  have h₁ :
      0 < pom_product_fold_additivity_collisionSum q d₁ :=
    pom_product_fold_additivity_collisionSum_pos q d₁ a ha
  have h₂ :
      0 < pom_product_fold_additivity_collisionSum q d₂ :=
    pom_product_fold_additivity_collisionSum_pos q d₂ b hb
  unfold pom_product_fold_additivity_collisionExponent
  rw [pom_product_fold_additivity_collisionSum_product, Nat.cast_mul]
  rw [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt h₁))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt h₂))]

lemma pom_product_fold_additivity_worstExponent_add {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (d₁ : α → ℕ) (d₂ : β → ℕ) (a : α) (b : β)
    (ha : 0 < d₁ a) (hb : 0 < d₂ b) :
    pom_product_fold_additivity_worstExponent (pom_product_fold_additivity_productFiber d₁ d₂) =
      pom_product_fold_additivity_worstExponent d₁ +
        pom_product_fold_additivity_worstExponent d₂ := by
  have hmax₁ : 0 < pom_product_fold_additivity_maxFiber d₁ := by
    unfold pom_product_fold_additivity_maxFiber
    exact lt_of_lt_of_le ha (Finset.le_sup (s := (Finset.univ : Finset α)) (f := d₁) (by simp))
  have hmax₂ : 0 < pom_product_fold_additivity_maxFiber d₂ := by
    unfold pom_product_fold_additivity_maxFiber
    exact lt_of_lt_of_le hb (Finset.le_sup (s := (Finset.univ : Finset β)) (f := d₂) (by simp))
  unfold pom_product_fold_additivity_worstExponent
  rw [pom_product_fold_additivity_maxFiber_product, Nat.cast_mul]
  rw [Real.log_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmax₁))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hmax₂))]

/-- Product-law package for finite collision sums, their logarithmic exponents, and the maximal
fiber multiplicity. This is the finite-layer seed used to model the additive exponent statements
from the paper's product-fold argument.
    prop:pom-product-fold-additivity -/
def pom_product_fold_additivity_statement : Prop :=
  ∀ {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β],
    ∀ (d₁ : α → ℕ) (d₂ : β → ℕ) (q : ℕ) [NeZero q],
      (∀ ab : α × β,
        pom_product_fold_additivity_productFiber d₁ d₂ ab = d₁ ab.1 * d₂ ab.2) ∧
      pom_product_fold_additivity_collisionSum q
          (pom_product_fold_additivity_productFiber d₁ d₂) =
        pom_product_fold_additivity_collisionSum q d₁ *
          pom_product_fold_additivity_collisionSum q d₂ ∧
      pom_product_fold_additivity_maxFiber
          (pom_product_fold_additivity_productFiber d₁ d₂) =
        pom_product_fold_additivity_maxFiber d₁ *
          pom_product_fold_additivity_maxFiber d₂ ∧
      ∀ a : α, ∀ b : β, 0 < d₁ a → 0 < d₂ b →
        pom_product_fold_additivity_collisionExponent q
            (pom_product_fold_additivity_productFiber d₁ d₂) =
          pom_product_fold_additivity_collisionExponent q d₁ +
            pom_product_fold_additivity_collisionExponent q d₂ ∧
        pom_product_fold_additivity_worstExponent
            (pom_product_fold_additivity_productFiber d₁ d₂) =
          pom_product_fold_additivity_worstExponent d₁ +
            pom_product_fold_additivity_worstExponent d₂

theorem paper_pom_product_fold_additivity : pom_product_fold_additivity_statement := by
  intro α β _ _ _ _ d₁ d₂ q _q
  refine ⟨?_, pom_product_fold_additivity_collisionSum_product q d₁ d₂,
    pom_product_fold_additivity_maxFiber_product d₁ d₂, ?_⟩
  · intro ab
    rfl
  · intro a b ha hb
    refine ⟨pom_product_fold_additivity_collisionExponent_add q d₁ d₂ a b ha hb,
      pom_product_fold_additivity_worstExponent_add d₁ d₂ a b ha hb⟩

end Omega.POM
