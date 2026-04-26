import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Finite active-support pressure `max (f(α)+aα)`, with a zero baseline. -/
def pom_spectrum_right_edge_support_function_pressure
    (phases : List (ℝ × ℝ)) (a : ℝ) : ℝ :=
  phases.foldr (fun phase acc => max (phase.2 + a * phase.1) acc) 0

/-- The zero-temperature gap obtained by subtracting the right edge `a α_*`. -/
def pom_spectrum_right_edge_support_function_gap
    (alphaStar : ℝ) (phases : List (ℝ × ℝ)) (a : ℝ) : ℝ :=
  pom_spectrum_right_edge_support_function_pressure phases a - a * alphaStar

/-- The support-function expression after the active support has been shifted by `α_*`. -/
def pom_spectrum_right_edge_support_function_support
    (alphaStar : ℝ) (phases : List (ℝ × ℝ)) (a : ℝ) : ℝ :=
  phases.foldr (fun phase acc => max (phase.2 - a * (alphaStar - phase.1)) acc)
    (0 - a * alphaStar)

lemma pom_spectrum_right_edge_support_function_max_sub
    (x y c : ℝ) : max x y - c = max (x - c) (y - c) := by
  rcases le_total x y with hxy | hyx
  · rw [max_eq_right hxy, max_eq_right]
    exact sub_le_sub_right hxy c
  · rw [max_eq_left hyx, max_eq_left]
    exact sub_le_sub_right hyx c

lemma pom_spectrum_right_edge_support_function_fold_shift
    (alphaStar : ℝ) (phases : List (ℝ × ℝ)) (a : ℝ) :
    pom_spectrum_right_edge_support_function_gap alphaStar phases a =
      pom_spectrum_right_edge_support_function_support alphaStar phases a := by
  unfold pom_spectrum_right_edge_support_function_gap
  induction phases with
  | nil =>
      simp [pom_spectrum_right_edge_support_function_pressure,
        pom_spectrum_right_edge_support_function_support]
  | cons phase phases ih =>
      simp only [pom_spectrum_right_edge_support_function_pressure,
        pom_spectrum_right_edge_support_function_support, List.foldr_cons]
      have ih' := ih
      simp only [pom_spectrum_right_edge_support_function_pressure,
        pom_spectrum_right_edge_support_function_support] at ih'
      rw [pom_spectrum_right_edge_support_function_max_sub, ih']
      ring_nf

/-- Concrete finite active-support form of the paper's support-function identity. -/
def pom_spectrum_right_edge_support_function_statement : Prop :=
  ∀ (alphaStar : ℝ) (phases : List (ℝ × ℝ)) (a : ℕ),
    pom_spectrum_right_edge_support_function_gap alphaStar phases (a : ℝ) =
      pom_spectrum_right_edge_support_function_support alphaStar phases (a : ℝ)

/-- Paper label: `thm:pom-spectrum-right-edge-support-function`. -/
theorem paper_pom_spectrum_right_edge_support_function :
    pom_spectrum_right_edge_support_function_statement := by
  intro alphaStar phases a
  exact pom_spectrum_right_edge_support_function_fold_shift alphaStar phases (a : ℝ)

end

end Omega.POM
