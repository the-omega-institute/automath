import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-grid and budget data for the pure phase packing law. -/
structure conclusion_boundary_finite_prime_pure_phase_packing_data where
  M : ℕ
  r : ℕ
  d : ℕ
  M_pos : 0 < M
  separatedCard : ℕ
  packingCapacity : ℕ
  logM : ℕ
  bitBudget : ℕ
  errorAllowance : ℕ
  separated_all_grid : separatedCard = M ^ r
  torus_packing_bound : separatedCard ≤ packingCapacity
  bit_budget_bound : r * logM ≤ d * bitBudget + errorAllowance

/-- The finite grid `Q_M^(r)` used in the packing statement. -/
abbrev conclusion_boundary_finite_prime_pure_phase_packing_grid
    (D : conclusion_boundary_finite_prime_pure_phase_packing_data) :=
  Fin D.r → Fin D.M

/-- Coordinate embedding of an `r`-grid into a `d`-torus grid when `r ≤ d`. -/
def conclusion_boundary_finite_prime_pure_phase_packing_coordinateEmbedding
    (D : conclusion_boundary_finite_prime_pure_phase_packing_data) (_h : D.r ≤ D.d)
    (x : conclusion_boundary_finite_prime_pure_phase_packing_grid D) : Fin D.d → Fin D.M :=
  fun i => if hi : i.val < D.r then x ⟨i.val, hi⟩ else ⟨0, D.M_pos⟩

/-- Concrete statement: cardinality, assumed packing and bit-budget inequalities, and the standard
coordinate embedding giving the achievability direction `r ≤ d`. -/
def conclusion_boundary_finite_prime_pure_phase_packing_statement
    (D : conclusion_boundary_finite_prime_pure_phase_packing_data) : Prop :=
  Fintype.card (conclusion_boundary_finite_prime_pure_phase_packing_grid D) = D.M ^ D.r ∧
    D.separatedCard ≤ D.packingCapacity ∧
    D.r * D.logM ≤ D.d * D.bitBudget + D.errorAllowance ∧
    (D.separatedCard =
        Fintype.card (conclusion_boundary_finite_prime_pure_phase_packing_grid D) →
      D.M ^ D.r ≤ D.packingCapacity) ∧
    (D.r ≤ D.d →
      ∃ embed :
          conclusion_boundary_finite_prime_pure_phase_packing_grid D → (Fin D.d → Fin D.M),
        Function.Injective embed)

/-- Paper label: `thm:conclusion-boundary-finite-prime-pure-phase-packing`. -/
theorem paper_conclusion_boundary_finite_prime_pure_phase_packing
    (D : conclusion_boundary_finite_prime_pure_phase_packing_data) :
    conclusion_boundary_finite_prime_pure_phase_packing_statement D := by
  classical
  unfold conclusion_boundary_finite_prime_pure_phase_packing_statement
  refine ⟨?_, D.torus_packing_bound, D.bit_budget_bound, ?_, ?_⟩
  · simp [conclusion_boundary_finite_prime_pure_phase_packing_grid]
  · intro hcard
    rw [← D.separated_all_grid]
    exact D.torus_packing_bound
  · intro hrd
    refine ⟨conclusion_boundary_finite_prime_pure_phase_packing_coordinateEmbedding D hrd, ?_⟩
    intro x y hxy
    funext j
    have hcoord := congrFun hxy (Fin.castLE hrd j)
    simpa [conclusion_boundary_finite_prime_pure_phase_packing_coordinateEmbedding, j.isLt]
      using hcoord

end Omega.Conclusion
