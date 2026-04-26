import Mathlib.Tactic

namespace Omega.Zeta

/-- Collapsed escort law on the two blocks: outside the max fiber and on the max fiber.
    thm:xi-terminal-fixed-freezing-tv-collapse -/
noncomputable def xi_terminal_fixed_freezing_tv_collapse_blockEscort (pMax : ℝ) : Bool → ℝ
  | false => 1 - pMax
  | true => pMax

/-- The zero-temperature limiting law: all mass lies on the maximal-fiber block.
    thm:xi-terminal-fixed-freezing-tv-collapse -/
noncomputable def xi_terminal_fixed_freezing_tv_collapse_groundBlock : Bool → ℝ
  | false => 0
  | true => 1

/-- Total variation distance on the collapsed two-block space.
    thm:xi-terminal-fixed-freezing-tv-collapse -/
noncomputable def xi_terminal_fixed_freezing_tv_collapse_tvDistance (p q : Bool → ℝ) : ℝ :=
  (|p false - q false| + |p true - q true|) / 2

/-- Max-fiber contribution divided by max-fiber plus residual contribution.
    thm:xi-terminal-fixed-freezing-tv-collapse -/
noncomputable def xi_terminal_fixed_freezing_tv_collapse_escortMaxMass
    (maxContribution residualContribution : ℝ) : ℝ :=
  maxContribution / (maxContribution + residualContribution)

/-- Concrete finite-block form of the fixed-freezing TV collapse. -/
def xi_terminal_fixed_freezing_tv_collapse_statement : Prop :=
  (∀ pMax : ℝ,
    0 ≤ pMax → pMax ≤ 1 →
      xi_terminal_fixed_freezing_tv_collapse_tvDistance
          (xi_terminal_fixed_freezing_tv_collapse_blockEscort pMax)
          xi_terminal_fixed_freezing_tv_collapse_groundBlock =
        1 - pMax) ∧
  (∀ maxContribution residualContribution epsilon : ℝ,
    0 < maxContribution →
      0 ≤ residualContribution →
      0 ≤ epsilon →
      residualContribution ≤ epsilon * maxContribution →
        1 -
            xi_terminal_fixed_freezing_tv_collapse_escortMaxMass
              maxContribution residualContribution ≤
          epsilon) ∧
  (∀ pMax Delta error : ℝ,
    0 ≤ pMax → pMax ≤ 1 →
      1 - pMax ≤ Real.exp (-Delta + error) →
        xi_terminal_fixed_freezing_tv_collapse_tvDistance
            (xi_terminal_fixed_freezing_tv_collapse_blockEscort pMax)
            xi_terminal_fixed_freezing_tv_collapse_groundBlock ≤
          Real.exp (-Delta + error))

/-- Paper label: `thm:xi-terminal-fixed-freezing-tv-collapse`.
On the max-fiber/residual two-block decomposition, total variation from the ground-state block is
exactly the residual mass. If the residual contribution is bounded by an exponential gap multiple
of the maximal contribution, the same bound controls the TV distance. -/
theorem paper_xi_terminal_fixed_freezing_tv_collapse :
    xi_terminal_fixed_freezing_tv_collapse_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro pMax hp0 hp1
    unfold xi_terminal_fixed_freezing_tv_collapse_tvDistance
      xi_terminal_fixed_freezing_tv_collapse_blockEscort
      xi_terminal_fixed_freezing_tv_collapse_groundBlock
    have hres_nonneg : 0 ≤ 1 - pMax := by linarith
    have htrue : |pMax - 1| = 1 - pMax := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hfalse : |1 - pMax - 0| = 1 - pMax := by
      simpa using abs_of_nonneg hres_nonneg
    rw [hfalse, htrue]
    ring
  · intro maxContribution residualContribution epsilon hmax hres heps hgap
    unfold xi_terminal_fixed_freezing_tv_collapse_escortMaxMass
    have hden_pos : 0 < maxContribution + residualContribution := by linarith
    have hidentity :
        1 - maxContribution / (maxContribution + residualContribution) =
          residualContribution / (maxContribution + residualContribution) := by
      field_simp [ne_of_gt hden_pos]
      ring
    rw [hidentity]
    rw [div_le_iff₀ hden_pos]
    nlinarith [hgap, mul_nonneg heps hres]
  · intro pMax Delta error hp0 hp1 hbound
    rw [(show
      xi_terminal_fixed_freezing_tv_collapse_tvDistance
          (xi_terminal_fixed_freezing_tv_collapse_blockEscort pMax)
          xi_terminal_fixed_freezing_tv_collapse_groundBlock =
        1 - pMax by
          unfold xi_terminal_fixed_freezing_tv_collapse_tvDistance
            xi_terminal_fixed_freezing_tv_collapse_blockEscort
            xi_terminal_fixed_freezing_tv_collapse_groundBlock
          have hres_nonneg : 0 ≤ 1 - pMax := by linarith
          have htrue : |pMax - 1| = 1 - pMax := by
            rw [abs_of_nonpos (by linarith)]
            ring
          have hfalse : |1 - pMax - 0| = 1 - pMax := by
            simpa using abs_of_nonneg hres_nonneg
          rw [hfalse, htrue]
          ring)]
    exact hbound

end Omega.Zeta
