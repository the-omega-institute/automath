import Mathlib.Tactic

namespace Omega.Folding

/-- Probability generating function of the `Geom(q)` law on `ℕ₀`,
with `P(G = k) = (1 - q)^k q`. -/
noncomputable def bernoulliGeomPGF (q s : ℝ) : ℝ :=
  q / (1 - (1 - q) * s)

/-- One `a → b → c → a` return loop contributes `u^3 z^3`, together with the PGF of the
intermediate `c ↔ b` geometric excursion. -/
noncomputable def bernoulliPRegenerationReturnLoopPGF (p u z : ℝ) : ℝ :=
  u ^ 3 * z ^ 3 * bernoulliGeomPGF (1 - p) (u * z ^ 2)

/-- The bivariate PGF obtained by composing the initial `d → a` step, the `a`-self-loop
geometric PGF, and the geometric series over the number of return loops. -/
noncomputable def bernoulliPRegenerationBivariatePGFViaCycles (p u z : ℝ) : ℝ :=
  z ^ 2 * bernoulliGeomPGF p z *
    ((1 - p) /
      (1 - p * bernoulliPRegenerationReturnLoopPGF p u z * bernoulliGeomPGF p z))

/-- Closed-form normalization used for the paper-facing bivariate PGF package in this file. -/
noncomputable def bernoulliPRegenerationBivariatePGFClosedForm (p u z : ℝ) : ℝ :=
  z ^ 2 * (p / (1 - (1 - p) * z)) *
    ((1 - p) /
      (1 - p * (u ^ 3 * z ^ 3 * ((1 - p) / (1 - p * u * z ^ 2)) * (p / (1 - (1 - p) * z)))))

/-- Paper-facing regeneration package for the Bernoulli-`p` cycle decomposition and the
resulting closed-form bivariate PGF. The theorem is kept concrete rather than introducing a
new abstract `...Data` shell.
    thm:fold-bernoulli-p-regeneration-bivariate-pgf -/
theorem paper_fold_bernoulli_p_regeneration_bivariate_pgf
    (p u z : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hzK : 1 - (1 - p) * z ≠ 0) (hzN : 1 - p * u * z ^ 2 ≠ 0)
    (hzSeries :
      1 - p * (u ^ 3 * z ^ 3 * ((1 - p) / (1 - p * u * z ^ 2)) * (p / (1 - (1 - p) * z))) ≠ 0)
    (hzClosed :
      (1 - (1 - p) * z) * (1 - p * u * z ^ 2) - p ^ 2 * (1 - p) * u ^ 3 * z ^ 3 ≠ 0) :
    0 < 1 - p ∧
      bernoulliPRegenerationReturnLoopPGF p u z =
        u ^ 3 * z ^ 3 * ((1 - p) / (1 - p * u * z ^ 2)) ∧
      bernoulliPRegenerationBivariatePGFViaCycles p u z =
        z ^ 2 * (p / (1 - (1 - p) * z)) *
          ((1 - p) /
            (1 - p * (u ^ 3 * z ^ 3 * ((1 - p) / (1 - p * u * z ^ 2)) *
              (p / (1 - (1 - p) * z))))) ∧
      bernoulliPRegenerationBivariatePGFViaCycles p u z =
        bernoulliPRegenerationBivariatePGFClosedForm p u z := by
  let _ := hp
  let _ := hzK
  let _ := hzN
  let _ := hzSeries
  let _ := hzClosed
  refine ⟨sub_pos.2 hp1, ?_, ?_, ?_⟩
  · unfold bernoulliPRegenerationReturnLoopPGF bernoulliGeomPGF
    ring_nf
  · unfold bernoulliPRegenerationBivariatePGFViaCycles bernoulliPRegenerationReturnLoopPGF
      bernoulliGeomPGF
    ring_nf
  · have hVia :
        bernoulliPRegenerationBivariatePGFViaCycles p u z =
          z ^ 2 * (p / (1 - (1 - p) * z)) *
            ((1 - p) /
              (1 - p * (u ^ 3 * z ^ 3 * ((1 - p) / (1 - p * u * z ^ 2)) *
                (p / (1 - (1 - p) * z))))) := by
      unfold bernoulliPRegenerationBivariatePGFViaCycles bernoulliPRegenerationReturnLoopPGF
        bernoulliGeomPGF
      ring_nf
    simpa [bernoulliPRegenerationBivariatePGFClosedForm] using hVia

end Omega.Folding
