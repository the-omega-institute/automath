import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Indicator of a finite off-slice packet. -/
def xi_offslice_indicators_additivity_indicator {n : ℕ} (A : Finset (Fin n)) (i : Fin n) : ℕ :=
  if i ∈ A then 1 else 0

/-- Additive packet weight. -/
def xi_offslice_indicators_additivity_weight {n : ℕ} (w : Fin n → ℕ)
    (A : Finset (Fin n)) : ℕ :=
  Finset.sum A fun i => w i

/-- Multiplicative Blaschke-origin modulus proxy over a packet. -/
def xi_offslice_indicators_additivity_origin_modulus {n : ℕ} (b : Fin n → ℚ)
    (A : Finset (Fin n)) : ℚ :=
  Finset.prod A fun i => b i

/-- Concrete additivity statement for disjoint off-slice packets. -/
def xi_offslice_indicators_additivity_statement (n : ℕ) : Prop :=
  ∀ A B : Finset (Fin n), Disjoint A B →
    (∀ i : Fin n,
      xi_offslice_indicators_additivity_indicator (A ∪ B) i =
        xi_offslice_indicators_additivity_indicator A i +
          xi_offslice_indicators_additivity_indicator B i) ∧
    (∀ w : Fin n → ℕ,
      xi_offslice_indicators_additivity_weight w (A ∪ B) =
        xi_offslice_indicators_additivity_weight w A +
          xi_offslice_indicators_additivity_weight w B) ∧
    (∀ b : Fin n → ℚ,
      xi_offslice_indicators_additivity_origin_modulus b (A ∪ B) =
        xi_offslice_indicators_additivity_origin_modulus b A *
          xi_offslice_indicators_additivity_origin_modulus b B)

/-- Paper label: `thm:xi-offslice-indicators-additivity`. -/
theorem xi_offslice_indicators_additivity_finite_packet_additivity (n : ℕ) :
    xi_offslice_indicators_additivity_statement n := by
  intro A B hdisj
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hnot : i ∈ A → i ∉ B := by
      exact fun hiA hiB => (Finset.disjoint_left.mp hdisj) hiA hiB
    by_cases hiA : i ∈ A
    · simp [xi_offslice_indicators_additivity_indicator, hiA, hnot hiA]
    · by_cases hiB : i ∈ B
      · simp [xi_offslice_indicators_additivity_indicator, hiA, hiB]
      · simp [xi_offslice_indicators_additivity_indicator, hiA, hiB]
  · intro w
    simp [xi_offslice_indicators_additivity_weight, Finset.sum_union hdisj]
  · intro b
    simp [xi_offslice_indicators_additivity_origin_modulus, Finset.prod_union hdisj]

end Omega.Zeta
