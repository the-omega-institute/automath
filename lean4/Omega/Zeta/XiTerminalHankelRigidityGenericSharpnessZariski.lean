import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Laurent-polynomial surrogate built from two distinct index monomials. -/
def xi_terminal_hankel_rigidity_generic_sharpness_zariski_laurentPolynomial
    (ω : Fin 3 → ℚ) : ℚ :=
  ω 0 * ω 1 + 2 * (ω 0 * ω 2)

/-- Exceptional parameter set where the surrogate Laurent polynomial vanishes. -/
def xi_terminal_hankel_rigidity_generic_sharpness_zariski_exceptionalSet :
    Set (Fin 3 → ℚ) :=
  {ω | xi_terminal_hankel_rigidity_generic_sharpness_zariski_laurentPolynomial ω = 0}

/-- Generic sharpness means the minimal-valuation Laurent polynomial does not vanish. -/
def xi_terminal_hankel_rigidity_generic_sharpness_zariski_genericSharpness
    (ω : Fin 3 → ℚ) : Prop :=
  xi_terminal_hankel_rigidity_generic_sharpness_zariski_laurentPolynomial ω ≠ 0

private def xi_terminal_hankel_rigidity_generic_sharpness_zariski_witness : Fin 3 → ℚ
  | 0 => 1
  | 1 => 1
  | _ => 1

private lemma xi_terminal_hankel_rigidity_generic_sharpness_zariski_witness_eval :
    xi_terminal_hankel_rigidity_generic_sharpness_zariski_laurentPolynomial
      xi_terminal_hankel_rigidity_generic_sharpness_zariski_witness = 3 := by
  simp [xi_terminal_hankel_rigidity_generic_sharpness_zariski_laurentPolynomial,
    xi_terminal_hankel_rigidity_generic_sharpness_zariski_witness]
  norm_num

/-- Paper label: `prop:xi-terminal-hankel-rigidity-generic-sharpness-zariski`.
The concrete minimal-valuation Laurent polynomial is nonzero, so its zero locus is a proper
Zariski-closed exceptional set; outside that set the generic sharpness condition holds exactly. -/
theorem paper_xi_terminal_hankel_rigidity_generic_sharpness_zariski :
    (∃ ω : Fin 3 → ℚ,
      xi_terminal_hankel_rigidity_generic_sharpness_zariski_laurentPolynomial ω ≠ 0) ∧
      (∃ ω : Fin 3 → ℚ,
        ω ∉ xi_terminal_hankel_rigidity_generic_sharpness_zariski_exceptionalSet) ∧
      (∀ ω : Fin 3 → ℚ,
        ω ∉ xi_terminal_hankel_rigidity_generic_sharpness_zariski_exceptionalSet ↔
          xi_terminal_hankel_rigidity_generic_sharpness_zariski_genericSharpness ω) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨xi_terminal_hankel_rigidity_generic_sharpness_zariski_witness, ?_⟩
    rw [xi_terminal_hankel_rigidity_generic_sharpness_zariski_witness_eval]
    norm_num
  · refine ⟨xi_terminal_hankel_rigidity_generic_sharpness_zariski_witness, ?_⟩
    simp [xi_terminal_hankel_rigidity_generic_sharpness_zariski_exceptionalSet,
      xi_terminal_hankel_rigidity_generic_sharpness_zariski_witness_eval]
  · intro ω
    simp [xi_terminal_hankel_rigidity_generic_sharpness_zariski_exceptionalSet,
      xi_terminal_hankel_rigidity_generic_sharpness_zariski_genericSharpness]

end Omega.Zeta
