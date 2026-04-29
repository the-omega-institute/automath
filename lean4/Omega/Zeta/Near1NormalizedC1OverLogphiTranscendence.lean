import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete near-one data for the normalized constant `c1 / log phi`.  The predicate
`TranscendentalOverQ` is supplied by the ambient development, together with the known
transcendence of `log 2 / log phi` and stability under subtracting rational algebraic terms. -/
structure near1_normalized_c1_over_logphi_transcendence_Data where
  TranscendentalOverQ : ℝ → Prop
  φ : ℝ
  log2_over_logphi : ℝ
  normalized_c1_over_logphi : ℝ
  log2_over_logphi_eq : log2_over_logphi = Real.log 2 / Real.log φ
  log2_over_logphi_transcendental : TranscendentalOverQ log2_over_logphi
  normalized_c1_over_logphi_eq : normalized_c1_over_logphi = log2_over_logphi - 1
  subtract_rational_preserves_transcendence :
    ∀ x q : ℝ,
      TranscendentalOverQ x →
        q ∈ Set.range (fun r : ℚ => (r : ℝ)) → TranscendentalOverQ (x - q)

namespace near1_normalized_c1_over_logphi_transcendence_Data

/-- The normalized `c1 / log phi` term is transcendental. -/
def normalized_c1_over_logphi_transcendental
    (D : near1_normalized_c1_over_logphi_transcendence_Data) : Prop :=
  D.TranscendentalOverQ D.normalized_c1_over_logphi

/-- Subtracting the rational algebraic shift `1` preserves the near-one transcendence input. -/
lemma subtract_one_preserves
    (D : near1_normalized_c1_over_logphi_transcendence_Data) :
    D.TranscendentalOverQ (D.log2_over_logphi - 1) := by
  exact
    D.subtract_rational_preserves_transcendence D.log2_over_logphi 1
      D.log2_over_logphi_transcendental ⟨1, by norm_num⟩

end near1_normalized_c1_over_logphi_transcendence_Data

open near1_normalized_c1_over_logphi_transcendence_Data

/-- Paper label: `cor:near1-normalized-c1-over-logphi-transcendence`. -/
theorem paper_near1_normalized_c1_over_logphi_transcendence
    (D : near1_normalized_c1_over_logphi_transcendence_Data) :
    D.normalized_c1_over_logphi_transcendental := by
  rw [normalized_c1_over_logphi_transcendental, D.normalized_c1_over_logphi_eq]
  exact D.subtract_one_preserves

end Omega.Zeta
