import Mathlib

namespace Omega.Experiments

/-- Minimal microstate package: `qMin m` dominates a gap functional, and that gap functional in
turn satisfies the Markov-style lower bound `c / m`. -/
structure MarkovControlledMicrostates (c : ℝ) where
  qMin : ℕ → ℝ
  minGap : ℕ → ℝ
  qMin_ge_minGap : ∀ m : ℕ, 1 ≤ m → minGap m ≤ qMin m
  minGap_ge_markov : ∀ m : ℕ, 1 ≤ m → c / m ≤ minGap m

/-- Paper-facing Markov lower bound for the smallest rotation microstate atom: once the atom size
is bounded below by a Markov-controlled gap functional, the golden branch specialization yields the
explicit lower bound `1 / (sqrt 5 * m)`.
    prop:qmin-lowerbound-markov -/
theorem paper_qmin_lowerbound_markov
    (M : MarkovControlledMicrostates (1 / Real.sqrt 5)) :
    ∀ m : ℕ, 1 ≤ m → 1 / (Real.sqrt 5 * m) ≤ M.qMin m := by
  intro m hm
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 from by omega)
  have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := ne_of_gt hsqrt5_pos
  have hmarkov : ((1 / Real.sqrt 5 : ℝ) / m) ≤ M.minGap m :=
    M.minGap_ge_markov m hm
  have hgap : M.minGap m ≤ M.qMin m := M.qMin_ge_minGap m hm
  have hrewrite : ((1 / Real.sqrt 5 : ℝ) / m) = 1 / (Real.sqrt 5 * m) := by
    field_simp [hm0, hsqrt5_ne]
  calc
    1 / (Real.sqrt 5 * m) = ((1 / Real.sqrt 5 : ℝ) / m) := hrewrite.symm
    _ ≤ M.minGap m := hmarkov
    _ ≤ M.qMin m := hgap

end Omega.Experiments
