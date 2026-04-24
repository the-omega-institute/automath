import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Zeta.FinitePartNyquistParsevalAliasing

namespace Omega.Conclusion

open Omega.Zeta
open scoped BigOperators

/-- Alias interaction between two support indices at Nyquist depth `q`. -/
noncomputable def conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum
    (support : Finset ℕ) (coeff : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ m ∈ support, ∑ n ∈ support,
    if m ≠ n ∧ m % q = n % q then coeff m * star (coeff n) else 0

/-- No two distinct support points collide modulo `q`. -/
def conclusion_torsion_sampling_nyquist_noalias_exactness_no_collision
    (support : Finset ℕ) (q : ℕ) : Prop :=
  ∀ ⦃m n : ℕ⦄, m ∈ support → n ∈ support → m ≠ n → m % q ≠ n % q

/-- The support lies strictly below the cutoff `Nstar`. -/
def conclusion_torsion_sampling_nyquist_noalias_exactness_below_cutoff
    (support : Finset ℕ) (Nstar : ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄, n ∈ support → n < Nstar

/-- Paper label: `thm:conclusion-torsion-sampling-nyquist-noalias-exactness`.

The Nyquist/Parseval identity splits the sampled energy into the main spectral term plus alias
interactions. If distinct support points never collide modulo `q`, every alias term vanishes. In
particular, any support contained in `{0, …, Nstar - 1}` is automatically collision-free once
`q > Nstar`. -/
theorem paper_conclusion_torsion_sampling_nyquist_noalias_exactness
    (support : Finset ℕ) (coeff : ℕ → ℂ) (main : ℂ) (q Nstar : ℕ) :
    let D : NyquistParsevalData := {
      spectralEnergy := main
      aliasingCorrection := fun q' =>
        conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum support coeff q'
    }
    D.discreteEnergy q =
        main + conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum support coeff q ∧
      (conclusion_torsion_sampling_nyquist_noalias_exactness_no_collision support q →
        conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum support coeff q = 0 ∧
          D.discreteEnergy q = main) ∧
      (conclusion_torsion_sampling_nyquist_noalias_exactness_below_cutoff support Nstar →
        Nstar < q →
          conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum support coeff q = 0 ∧
            D.discreteEnergy q = main) := by
  dsimp
  let D : NyquistParsevalData := {
    spectralEnergy := main
    aliasingCorrection := fun q' =>
      conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum support coeff q'
  }
  have hParseval := paper_finite_part_nyquist_parseval_aliasing D q
  have hNoCollisionExact :
      conclusion_torsion_sampling_nyquist_noalias_exactness_no_collision support q →
        conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum support coeff q = 0 ∧
          D.discreteEnergy q = main := by
    intro hNoCollision
    have hAliasZero :
        conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum support coeff q = 0 := by
      unfold conclusion_torsion_sampling_nyquist_noalias_exactness_alias_sum
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro n hn
      by_cases hmn : m ≠ n
      · have hmod : m % q ≠ n % q := hNoCollision hm hn hmn
        simp [hmn, hmod]
      · simp [hmn]
    refine ⟨hAliasZero, ?_⟩
    simp [D, NyquistParsevalData.discreteEnergy, hAliasZero]
  refine ⟨hParseval.2, hNoCollisionExact, ?_⟩
  · intro hBelow hq
    have hNoCollision :
        conclusion_torsion_sampling_nyquist_noalias_exactness_no_collision support q := by
      intro m n hm hn hmn hmod
      have hm_lt_q : m < q := lt_trans (hBelow hm) hq
      have hn_lt_q : n < q := lt_trans (hBelow hn) hq
      apply hmn
      calc
        m = m % q := by symm; exact Nat.mod_eq_of_lt hm_lt_q
        _ = n % q := hmod
        _ = n := Nat.mod_eq_of_lt hn_lt_q
    exact hNoCollisionExact hNoCollision

end Omega.Conclusion
