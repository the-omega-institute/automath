import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete projective-transfer data for the integer `q` denominator-annihilation identity. -/
structure xi_time_part9zj_integer_q_projective_bridge_denominator_annihilation_data where
  Output : Type
  outputFintype : Fintype Output
  State : Type
  q : ℕ
  p : State → ℝ
  B : Output → State → State
  g : Output → State → ℝ
  Phi : Output → State → State
  L : (State → ℝ) → State → ℝ
  g_nonneg : ∀ b w, 0 ≤ g b w
  homogeneity :
    ∀ b w, 0 < g b w → p (Phi b w) = p (B b w) / (g b w) ^ q
  zero_bucket : ∀ b w, g b w = 0 → p (B b w) = 0
  transfer_def :
    ∀ w,
      L p w =
        ∑ b : Output, if g b w = 0 then 0 else (g b w) ^ q * p (Phi b w)

/-- The integer homogeneous layer has no surviving projective denominator. -/
def xi_time_part9zj_integer_q_projective_bridge_denominator_annihilation_statement
    (D : xi_time_part9zj_integer_q_projective_bridge_denominator_annihilation_data) :
    Prop :=
  letI := D.outputFintype
  ∀ w, D.L D.p w = ∑ b : D.Output, D.p (D.B b w)

/-- Paper label: `thm:xi-time-part9zj-integer-q-projective-bridge-denominator-annihilation`. -/
theorem paper_xi_time_part9zj_integer_q_projective_bridge_denominator_annihilation
    (D : xi_time_part9zj_integer_q_projective_bridge_denominator_annihilation_data) :
    xi_time_part9zj_integer_q_projective_bridge_denominator_annihilation_statement D := by
  classical
  letI := D.outputFintype
  intro w
  rw [D.transfer_def w]
  refine Finset.sum_congr rfl ?_
  intro b _hb
  by_cases hzero : D.g b w = 0
  · simp [hzero, D.zero_bucket b w hzero]
  · have hpos : 0 < D.g b w := by
      exact lt_of_le_of_ne (D.g_nonneg b w) (fun h => hzero h.symm)
    have hpow : (D.g b w) ^ D.q ≠ 0 := pow_ne_zero D.q (ne_of_gt hpos)
    rw [if_neg hzero, D.homogeneity b w hpos]
    field_simp [hpow]

end

end Omega.Zeta
