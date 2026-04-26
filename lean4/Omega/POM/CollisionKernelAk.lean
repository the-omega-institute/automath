import Mathlib

namespace Omega.POM

/-- One synchronized `k`-fold transition of a deterministic finite transducer. -/
def pom_collision_kernel_ak_synchronizedStep
    {Q α : Type} {k : ℕ} (δ : Q → α → Q)
    (x : Fin k → Q) (a : Fin k → α) : Fin k → Q :=
  fun i => δ (x i) (a i)

/-- The equal-output constraint for the synchronized product. -/
def pom_collision_kernel_ak_equalOutput
    {Q α β : Type} {k : ℕ} (out : Q → α → β)
    (x : Fin k → Q) (a : Fin k → α) : Prop :=
  ∀ i j : Fin k, out (x i) (a i) = out (x j) (a j)

/-- The finite transition count from one synchronized state to another. -/
noncomputable def pom_collision_kernel_ak_transitionCount
    {Q α β : Type} [Fintype α] {k : ℕ}
    (δ : Q → α → Q) (out : Q → α → β) (x y : Fin k → Q) : ℕ :=
  by
    classical
    exact
      (Finset.univ.filter fun a : Fin k → α =>
        pom_collision_kernel_ak_synchronizedStep δ x a = y ∧
          pom_collision_kernel_ak_equalOutput out x a).card

/-- Concrete finite-state collision-kernel package: the synchronized product has finite transition
counts bounded by the number of input tuples. -/
def pom_collision_kernel_ak_statement : Prop :=
  ∀ {Q α β : Type} [Fintype α]
    (k : ℕ) (_hk : 2 ≤ k) (δ : Q → α → Q) (out : Q → α → β),
      ∃ N : ℕ, ∀ x y : Fin k → Q,
        pom_collision_kernel_ak_transitionCount δ out x y ≤ N

theorem paper_pom_collision_kernel_ak : pom_collision_kernel_ak_statement := by
  intro Q α β _ k _hk δ out
  refine ⟨Fintype.card (Fin k → α), ?_⟩
  intro x y
  classical
  exact Finset.card_filter_le _ _

end Omega.POM
