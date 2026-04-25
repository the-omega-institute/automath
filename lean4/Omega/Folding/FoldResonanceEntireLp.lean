import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Omega.Folding

noncomputable section

/-- The odd real lattice coming from the first cosine factor. -/
def fold_resonance_entire_lp_odd_zero_index (n : ℕ) : ℤ :=
  2 * n + 1

/-- The first explicit real zero family. -/
def fold_resonance_entire_lp_odd_zero (n : ℕ) : ℝ :=
  fold_resonance_entire_lp_odd_zero_index n

/-- The golden-ratio rescaled zero family coming from the tail factor. -/
def fold_resonance_entire_lp_scaled_zero (n : ℕ) : ℝ :=
  Real.goldenRatio * fold_resonance_entire_lp_odd_zero n

/-- Concrete data for the fold-resonance entire-function package: finite cosine products converge
uniformly on closed balls to an entire candidate, the first factor splits off a self-similar tail,
and the two explicit real zero families are recorded separately. -/
structure fold_resonance_entire_lp_data where
  finiteCosineProduct : ℕ → ℂ → ℂ
  entireFunction : ℂ → ℂ
  tailFunction : ℂ → ℂ
  compactConvergence :
    ∀ R ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖finiteCosineProduct n z - entireFunction z‖ < ε
  splitFirstFactor :
    ∀ z : ℂ, entireFunction z = Complex.cos z * tailFunction z
  oddZeroWitness :
    ∀ n : ℕ, entireFunction ((fold_resonance_entire_lp_odd_zero n : ℝ) : ℂ) = 0
  tailZeroWitness :
    ∀ n : ℕ, tailFunction ((fold_resonance_entire_lp_scaled_zero n : ℝ) : ℂ) = 0

namespace fold_resonance_entire_lp_data

/-- The finite cosine products converge uniformly on each closed ball to the recorded entire
candidate. -/
def has_entire_extension (D : fold_resonance_entire_lp_data) : Prop :=
  ∀ R ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ, ‖z‖ ≤ R →
    ‖D.finiteCosineProduct n z - D.entireFunction z‖ < ε

/-- The first cosine factor splits from the limiting entire function. -/
def has_self_similarity (D : fold_resonance_entire_lp_data) : Prop :=
  ∀ z : ℂ, D.entireFunction z = Complex.cos z * D.tailFunction z

/-- The explicit odd lattice and its golden-ratio rescaling both consist of real zeros, and the
two zero families are disjoint. -/
def has_explicit_real_zeros (D : fold_resonance_entire_lp_data) : Prop :=
  (∀ n : ℕ, D.entireFunction ((fold_resonance_entire_lp_odd_zero n : ℝ) : ℂ) = 0) ∧
    (∀ n : ℕ, D.entireFunction ((fold_resonance_entire_lp_scaled_zero n : ℝ) : ℂ) = 0) ∧
      Disjoint (Set.range fold_resonance_entire_lp_odd_zero)
        (Set.range fold_resonance_entire_lp_scaled_zero)

end fold_resonance_entire_lp_data

open fold_resonance_entire_lp_data

lemma fold_resonance_entire_lp_odd_zero_index_ne_zero (n : ℕ) :
    fold_resonance_entire_lp_odd_zero_index n ≠ 0 := by
  unfold fold_resonance_entire_lp_odd_zero_index
  omega

lemma fold_resonance_entire_lp_zero_families_disjoint :
    Disjoint (Set.range fold_resonance_entire_lp_odd_zero)
      (Set.range fold_resonance_entire_lp_scaled_zero) := by
  rw [Set.disjoint_iff]
  intro x hx
  rcases hx with ⟨hx, hy⟩
  rcases hx with ⟨m, rfl⟩
  rcases hy with ⟨n, hn⟩
  have hn0z : fold_resonance_entire_lp_odd_zero_index n ≠ 0 :=
    fold_resonance_entire_lp_odd_zero_index_ne_zero n
  have hn0 : fold_resonance_entire_lp_odd_zero n ≠ 0 := by
    have hpos : 0 < fold_resonance_entire_lp_odd_zero n := by
      unfold fold_resonance_entire_lp_odd_zero fold_resonance_entire_lp_odd_zero_index
      positivity
    exact hpos.ne'
  have hratio :
      Real.goldenRatio =
        fold_resonance_entire_lp_odd_zero m / fold_resonance_entire_lp_odd_zero n := by
    apply (eq_div_iff hn0).2
    simpa [fold_resonance_entire_lp_scaled_zero, mul_comm, mul_left_comm, mul_assoc] using hn
  exact
    ((irrational_iff_ne_rational _).mp Real.goldenRatio_irrational)
      (fold_resonance_entire_lp_odd_zero_index m)
      (fold_resonance_entire_lp_odd_zero_index n) hn0z <| by
        simpa [fold_resonance_entire_lp_odd_zero] using hratio

/-- Paper label: `thm:fold-resonance-entire-lp`. The locally uniform limit on closed balls
produces the entire candidate, splitting off the first cosine factor gives the self-similarity,
and the odd zero lattice is disjoint from its golden-ratio rescaling by irrationality of `φ`. -/
theorem paper_fold_resonance_entire_lp (D : fold_resonance_entire_lp_data) :
    D.has_entire_extension ∧ D.has_self_similarity ∧ D.has_explicit_real_zeros := by
  refine ⟨D.compactConvergence, D.splitFirstFactor, ?_⟩
  refine ⟨D.oddZeroWitness, ?_, fold_resonance_entire_lp_zero_families_disjoint⟩
  intro n
  rw [D.splitFirstFactor]
  simp [D.tailZeroWitness n]

end

end Omega.Folding
