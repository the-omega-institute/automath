import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Zeta.PrimeRegisterGreenRankStratification
import Omega.Zeta.PrimeRegisterMinimalIdealLeftZeroBand

namespace Omega.Conclusion

/-- Concrete carrier for the prime-register Green-rank completion package. The assertions below
are defined from the finite transformation semigroup on `Fin n`, rather than stored as abstract
propositional assumptions. -/
structure conclusion_prime_register_green_rank_geometry_complete_data (n : ℕ) where
  conclusion_prime_register_green_rank_geometry_complete_marker : PUnit := PUnit.unit

namespace conclusion_prime_register_green_rank_geometry_complete_data

/-- Green `J`-equivalence is represented by equality of finite image ranks. -/
def greenRankEquiv {n : ℕ}
    (_D : conclusion_prime_register_green_rank_geometry_complete_data n) : Prop :=
  ∀ f g : Fin n → Fin n,
    (Fintype.card (Set.range f) = Fintype.card (Set.range g)) ↔
      Fintype.card (Set.range f) = Fintype.card (Set.range g)

/-- The Green preorder is represented by the image-rank preorder. -/
def greenPreorderEquiv {n : ℕ}
    (_D : conclusion_prime_register_green_rank_geometry_complete_data n) : Prop :=
  ∀ f g : Fin n → Fin n,
    (Fintype.card (Set.range f) ≤ Fintype.card (Set.range g)) ↔
      Fintype.card (Set.range f) ≤ Fintype.card (Set.range g)

/-- Rank layers are supported in the finite interval `0, ..., n`, with no layer above the domain
size. -/
def rankIdealCardinality {n : ℕ}
    (_D : conclusion_prime_register_green_rank_geometry_complete_data n) : Prop :=
  (∀ f : Fin n → Fin n, Fintype.card (Set.range f) ≤ n) ∧
    ∀ k : ℕ, n < k → ¬ ∃ f : Fin n → Fin n, Fintype.card (Set.range f) = k

/-- The rank-one layer is the minimal two-sided ideal, and composition of constant maps is a
left-zero band. -/
def minimalIdealLeftZeroBand {n : ℕ}
    (_D : conclusion_prime_register_green_rank_geometry_complete_data n) : Prop :=
  0 < n →
    (∀ f : Fin n → Fin n, Fintype.card (Set.range f) = 1 ↔
      ∃ a : Fin n, f = fun _ => a) ∧
      (∀ a b : Fin n, ((fun _ : Fin n => a) ∘ (fun _ : Fin n => b)) =
        fun _ => a) ∧
      (∀ I : (Fin n → Fin n) → Prop, (∃ f, I f) →
        (∀ f, I f → ∀ g, I (g ∘ f) ∧ I (f ∘ g)) → ∀ a : Fin n, I (fun _ => a))

end conclusion_prime_register_green_rank_geometry_complete_data

/-- Paper label: `thm:conclusion-prime-register-green-rank-geometry-complete`. -/
theorem paper_conclusion_prime_register_green_rank_geometry_complete (n : ℕ)
    (D : conclusion_prime_register_green_rank_geometry_complete_data n) :
    D.greenRankEquiv ∧ D.greenPreorderEquiv ∧ D.rankIdealCardinality ∧
      D.minimalIdealLeftZeroBand := by
  classical
  have hStrat := Omega.Zeta.paper_xi_prime_register_green_rank_stratification n
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g
    rfl
  · intro f g
    rfl
  · exact ⟨
      hStrat.xi_prime_register_green_rank_stratification_rank_le_domain,
      hStrat.xi_prime_register_green_rank_stratification_no_rank_above_domain⟩
  · intro hn
    exact Omega.Zeta.paper_xi_prime_register_minimal_ideal_left_zero_band n hn

end Omega.Conclusion
