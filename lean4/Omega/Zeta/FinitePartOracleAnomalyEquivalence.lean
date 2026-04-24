import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Zeta.FinitePartResidueDriftTrichotomy

namespace Omega.Zeta

/-- Oracle-side formulation of the sublinear finite-part residue drift guaranteed by the residue
trichotomy package. -/
def FinitePartOracleTame (_rho _d C : ℕ → Real) (_c : Real) : Prop :=
  ∀ eps > 0, ∃ N, ∀ q ≥ N, |Real.log (C q)| ≤ eps * (q : Real)

/-- A concrete linear anomaly witness: some positive slope persists along the `|log C_q| / q`
scale. -/
def FinitePartOracleAnomaly (C : ℕ → Real) : Prop :=
  ∃ α > 0, ∃ N : ℕ, ∀ q ≥ N, α * (q : Real) ≤ |Real.log (C q)|

/-- Paper label: `cor:finite-part-oracle-anomaly-equivalence`. Under the same growth and squeeze
hypotheses used in the residue-drift trichotomy, the oracle statement "all tails are eventually
sublinear" is equivalent to exclusion of any persistent linear anomaly witness. -/
theorem paper_finite_part_oracle_anomaly_equivalence
    (rho d C : ℕ → Real) (c : Real)
    (hc : 1 < c) (hrho_pos : ∃ N, ∀ q ≥ N, 0 < rho q) (hC_pos : ∃ N, ∀ q ≥ N, 0 < C q)
    (hrho : ∃ N, ∀ q ≥ N, c ^ q ≤ rho q)
    (hd : ∀ eps > 0, ∃ N, ∀ q ≥ N, d q ≤ Real.exp (eps * (q : Real)))
    (hsqueeze : ∃ N, ∀ q ≥ N, |Real.log (C q)| ≤ 2 * d q / Real.sqrt (rho q)) :
    FinitePartOracleTame rho d C c ↔ ¬ FinitePartOracleAnomaly C := by
  have htame : FinitePartOracleTame rho d C c :=
    paper_finite_part_residue_drift_trichotomy rho d C c hc hrho_pos hC_pos hrho hd hsqueeze
  constructor
  · intro hTame hAnom
    rcases hAnom with ⟨α, hα, Nα, hαN⟩
    obtain ⟨Nε, hε⟩ := hTame (α / 2) (by positivity)
    let q := max Nα Nε + 1
    have hqα : q ≥ Nα := by
      dsimp [q]
      exact le_trans (le_max_left _ _) (Nat.le_succ _)
    have hqε : q ≥ Nε := by
      dsimp [q]
      exact le_trans (le_max_right _ _) (Nat.le_succ _)
    have hLower := hαN q hqα
    have hUpper := hε q hqε
    have hqpos : (0 : Real) < q := by
      dsimp [q]
      exact_mod_cast Nat.succ_pos (max Nα Nε)
    have hstrict : α / 2 * (q : Real) < α * (q : Real) := by
      nlinarith
    have : α * (q : Real) < α * (q : Real) := lt_of_le_of_lt hLower (lt_of_le_of_lt hUpper hstrict)
    exact (lt_irrefl _ this).elim
  · intro _
    exact htame

end Omega.Zeta
