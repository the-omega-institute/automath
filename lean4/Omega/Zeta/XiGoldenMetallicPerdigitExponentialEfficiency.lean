import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MetallicTwoStateSFT
import Omega.Kronecker.MetallicGap

namespace Omega.Zeta

open Omega.Folding

noncomputable section

/-- Per-digit exponential efficiency for the real metallic branch. -/
def xi_golden_metallic_perdigit_exponential_efficiency_eta (A : ℝ) : ℝ :=
  Real.log (metallicPerronRoot A) / A

/-- The exponential envelope determined by the golden endpoint. -/
def xi_golden_metallic_perdigit_exponential_efficiency_goldenEnvelope (A : ℝ) : ℝ :=
  Real.exp (A * Real.log Real.goldenRatio)

/-- Concrete corollary package for golden endpoint per-digit efficiency. -/
def xi_golden_metallic_perdigit_exponential_efficiency_statement : Prop :=
  StrictAntiOn xi_golden_metallic_perdigit_exponential_efficiency_eta (Set.Ici 1) ∧
    (∀ A : ℝ, 1 < A →
      xi_golden_metallic_perdigit_exponential_efficiency_eta A <
        xi_golden_metallic_perdigit_exponential_efficiency_eta 1 ∧
      metallicPerronRoot A <
        xi_golden_metallic_perdigit_exponential_efficiency_goldenEnvelope A) ∧
    xi_golden_metallic_perdigit_exponential_efficiency_eta 1 =
      Real.log Real.goldenRatio

lemma xi_golden_metallic_perdigit_exponential_efficiency_root_gt_one {A : ℝ}
    (hA : 1 ≤ A) : 1 < metallicPerronRoot A := by
  have hsq : (2 : ℝ) ^ 2 < A ^ 2 + 4 := by
    nlinarith [sq_nonneg A]
  have hsqrt : 2 < Real.sqrt (A ^ 2 + 4) := by
    have h' : Real.sqrt ((2 : ℝ) ^ 2) < Real.sqrt (A ^ 2 + 4) := by
      exact Real.sqrt_lt_sqrt (by positivity) hsq
    simpa using h'
  rw [metallicPerronRoot]
  nlinarith

/-- Paper label: `cor:xi-golden-metallic-perdigit-exponential-efficiency`. -/
theorem paper_xi_golden_metallic_perdigit_exponential_efficiency :
    xi_golden_metallic_perdigit_exponential_efficiency_statement := by
  have hroot_one : metallicPerronRoot (1 : ℝ) = Real.goldenRatio := by
    rw [metallicPerronRoot, Real.goldenRatio]
    norm_num
  have heta_one :
      xi_golden_metallic_perdigit_exponential_efficiency_eta 1 =
        Real.log Real.goldenRatio := by
    simp [xi_golden_metallic_perdigit_exponential_efficiency_eta, hroot_one]
  have hanti :
      StrictAntiOn xi_golden_metallic_perdigit_exponential_efficiency_eta (Set.Ici 1) := by
    intro A hA B hB hlt
    have hgap :=
      Omega.Kronecker.paper_kronecker_metallic_gap hA hB hlt
    have hA_pos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA
    have hB_pos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hB
    have hlogA_pos : 0 < Real.log (metallicPerronRoot A) := by
      exact Real.log_pos
        (xi_golden_metallic_perdigit_exponential_efficiency_root_gt_one hA)
    have hlogB_pos : 0 < Real.log (metallicPerronRoot B) := by
      exact Real.log_pos
        (xi_golden_metallic_perdigit_exponential_efficiency_root_gt_one hB)
    have hlogA_ne : Real.log (metallicPerronRoot A) ≠ 0 := hlogA_pos.ne'
    have hlogB_ne : Real.log (metallicPerronRoot B) ≠ 0 := hlogB_pos.ne'
    have hcross : A * Real.log (metallicPerronRoot B) <
        B * Real.log (metallicPerronRoot A) := by
      have htmp := hgap
      field_simp [hlogA_ne, hlogB_ne] at htmp
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
    rw [xi_golden_metallic_perdigit_exponential_efficiency_eta,
      xi_golden_metallic_perdigit_exponential_efficiency_eta]
    exact (div_lt_div_iff₀ hB_pos hA_pos).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcross)
  refine ⟨hanti, ?_, heta_one⟩
  intro A hA
  have hA_mem : A ∈ Set.Ici (1 : ℝ) := le_of_lt hA
  have h1_mem : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := by simp
  have heta_lt :
      xi_golden_metallic_perdigit_exponential_efficiency_eta A <
        xi_golden_metallic_perdigit_exponential_efficiency_eta 1 :=
    hanti h1_mem hA_mem hA
  have hlog_lt : Real.log (metallicPerronRoot A) < A * Real.log Real.goldenRatio := by
    have hA_pos : (0 : ℝ) < A := lt_trans zero_lt_one hA
    have htmp := (div_lt_iff₀ hA_pos).1 (by
      simpa [xi_golden_metallic_perdigit_exponential_efficiency_eta, heta_one] using
        heta_lt)
    simpa [hroot_one, mul_comm] using htmp
  have hroot_pos : 0 < metallicPerronRoot A := by
    exact lt_trans zero_lt_one
      (xi_golden_metallic_perdigit_exponential_efficiency_root_gt_one (le_of_lt hA))
  have hroot_lt :
      metallicPerronRoot A <
        xi_golden_metallic_perdigit_exponential_efficiency_goldenEnvelope A := by
    rw [xi_golden_metallic_perdigit_exponential_efficiency_goldenEnvelope]
    calc
      metallicPerronRoot A = Real.exp (Real.log (metallicPerronRoot A)) := by
        rw [Real.exp_log hroot_pos]
      _ < Real.exp (A * Real.log Real.goldenRatio) := Real.exp_lt_exp.mpr hlog_lt
  exact ⟨heta_lt, hroot_lt⟩

end

end Omega.Zeta
