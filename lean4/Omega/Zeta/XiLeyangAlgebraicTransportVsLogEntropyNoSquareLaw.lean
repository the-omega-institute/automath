import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-leyang-algebraic-transport-vs-log-entropy-no-square-law`. -/
theorem paper_xi_leyang_algebraic_transport_vs_log_entropy_no_square_law
    (AlgebraicOverQ TranscendentalOverQ : ℝ → Prop) (T c : ℝ)
    (hT : AlgebraicOverQ T)
    (hc2 : TranscendentalOverQ (c ^ 2))
    (hmul :
      ∀ r x : ℝ,
        AlgebraicOverQ r → r ≠ 0 → TranscendentalOverQ x → TranscendentalOverQ (r * x))
    (hdisjoint : ∀ x : ℝ, AlgebraicOverQ x → TranscendentalOverQ x → False) :
    ∀ r : ℝ, AlgebraicOverQ r → r ≠ 0 → T ≠ r * c ^ 2 := by
  intro r hr hr_ne hT_eq
  have htrans : TranscendentalOverQ (r * c ^ 2) := hmul r (c ^ 2) hr hr_ne hc2
  have hTtrans : TranscendentalOverQ T := by
    simpa [hT_eq] using htrans
  exact hdisjoint T hT hTtrans

end Omega.Zeta
