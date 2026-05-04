import Mathlib.Tactic

namespace Omega.Zeta

universe u v

/-- The finite-level component view: level `k` sees exactly coordinates whose birth index is
at most `k`. -/
abbrev xi_dyadic_fibonacci_completion_stable_local_splitting_level
    (I : Type u) (birth : I → ℕ) (α : I → Type v) (k : ℕ) : Type (max u v) :=
  (i : I) → birth i ≤ k → α i

/-- A componentwise inverse-limit point is a compatible choice at every finite level.  The
compatibility is stated as eventual coordinate stability, so all visible incarnations of a
coordinate agree after its first appearance. -/
abbrev xi_dyadic_fibonacci_completion_stable_local_splitting_limit
    (I : Type u) (birth : I → ℕ) (α : I → Type v) : Type (max u v) :=
  {x : ∀ k,
      xi_dyadic_fibonacci_completion_stable_local_splitting_level I birth α k //
    ∀ k l i (hk : birth i ≤ k) (hl : birth i ≤ l), x k i hk = x l i hl}

/-- Send a full product point to the compatible finite-level tower by restriction. -/
def xi_dyadic_fibonacci_completion_stable_local_splitting_productToLimit
    {I : Type u} (birth : I → ℕ) (α : I → Type v) (a : ∀ i, α i) :
    xi_dyadic_fibonacci_completion_stable_local_splitting_limit I birth α :=
  ⟨fun _ i _ => a i, by intro k l i hk hl; rfl⟩

/-- Read a compatible tower at the first level where each coordinate appears. -/
def xi_dyadic_fibonacci_completion_stable_local_splitting_limitToProduct
    {I : Type u} (birth : I → ℕ) (α : I → Type v)
    (x : xi_dyadic_fibonacci_completion_stable_local_splitting_limit I birth α) :
    ∀ i, α i :=
  fun i => x.1 (birth i) i le_rfl

/-- The componentwise product is equivalent to the inverse limit of stabilized finite levels. -/
noncomputable def xi_dyadic_fibonacci_completion_stable_local_splitting_limitProductEquiv
    {I : Type u} (birth : I → ℕ) (α : I → Type v) :
    xi_dyadic_fibonacci_completion_stable_local_splitting_limit I birth α ≃ (∀ i, α i) where
  toFun :=
    xi_dyadic_fibonacci_completion_stable_local_splitting_limitToProduct birth α
  invFun :=
    xi_dyadic_fibonacci_completion_stable_local_splitting_productToLimit birth α
  left_inv := by
    intro x
    apply Subtype.ext
    funext k i hk
    exact (x.2 k (birth i) i hk le_rfl).symm
  right_inv := by
    intro a
    rfl

/-- Paper label: `thm:xi-dyadic-fibonacci-completion-stable-local-splitting`.
Once each coordinate has a first visible level, the compatible finite-level tower is recovered
componentwise from the product of the stabilized local coordinates, and visible coordinates are
unchanged by moving between levels after birth. -/
theorem paper_xi_dyadic_fibonacci_completion_stable_local_splitting
    {I : Type u} (birth : I → ℕ) (α : I → Type v) :
    Nonempty
        (xi_dyadic_fibonacci_completion_stable_local_splitting_limit I birth α ≃
          (∀ i, α i)) ∧
      (∀ x : xi_dyadic_fibonacci_completion_stable_local_splitting_limit I birth α,
        ∀ k l i (hk : birth i ≤ k) (hl : birth i ≤ l), x.1 k i hk = x.1 l i hl) ∧
      (∀ a : ∀ i, α i,
        xi_dyadic_fibonacci_completion_stable_local_splitting_limitToProduct birth α
            (xi_dyadic_fibonacci_completion_stable_local_splitting_productToLimit birth α a) =
          a) := by
  refine ⟨⟨xi_dyadic_fibonacci_completion_stable_local_splitting_limitProductEquiv birth α⟩,
    ?_, ?_⟩
  · intro x k l i hk hl
    exact x.2 k l i hk hl
  · intro a
    rfl

end Omega.Zeta
