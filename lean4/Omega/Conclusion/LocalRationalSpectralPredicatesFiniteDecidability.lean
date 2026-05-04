import Mathlib.Tactic

namespace Omega.Conclusion

universe u

/-- The finite Taylor/moment prefix of length `M`. -/
def conclusion_local_rational_spectral_predicates_finite_decidability_prefix
    {Coeff : Type u} (M : ℕ) (coeff : ℕ → Coeff) : Fin M → Coeff :=
  fun j => coeff j

/-- Paper label: `cor:conclusion-local-rational-spectral-predicates-finite-decidability`.
If the finite Taylor/moment prefix on which a Boolean spectral predicate depends stabilizes
along a certificate tower, then the predicate itself is eventually constant. -/
theorem paper_conclusion_local_rational_spectral_predicates_finite_decidability
    {Coeff : Type u} (tower : ℕ → ℕ → Coeff) (limit : ℕ → Coeff) (M : ℕ)
    (predicate : (Fin M → Coeff) → Bool)
    (hstable : ∃ L₀, ∀ L (j : Fin M), L₀ ≤ L → tower L j = limit j) :
    ∃ L₀ b, ∀ L, L₀ ≤ L →
      predicate
          (conclusion_local_rational_spectral_predicates_finite_decidability_prefix M
            (tower L)) =
        b := by
  rcases hstable with ⟨L₀, hL₀⟩
  refine ⟨L₀,
    predicate (conclusion_local_rational_spectral_predicates_finite_decidability_prefix M limit),
    ?_⟩
  intro L hL
  congr 1
  funext j
  exact hL₀ L j hL

end Omega.Conclusion
