import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Folding.GmFischerCover

namespace Omega.Folding

open scoped BigOperators

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the `Φ_m` Parry package: irreducibility and Perron-Frobenius
data give the Parry measure, and the cylinder formula follows from that measure.
    prop:Phi_m-parry -/
theorem paper_phi_m_parry_measure
    (m : Nat) (coverIrreducible pfEigenData parryMeasure cylinderFormula : Prop)
    (hParry : coverIrreducible -> pfEigenData -> parryMeasure)
    (hCyl : parryMeasure -> cylinderFormula) :
    coverIrreducible -> pfEigenData -> parryMeasure ∧ cylinderFormula := by
  let _ := m
  intro hCover hPf
  have hParryMeasure : parryMeasure := hParry hCover hPf
  exact ⟨hParryMeasure, hCyl hParryMeasure⟩

/-- Finite Perron--Frobenius data for the `Φ_m` cover graph. -/
structure phi_m_parry_data (V : Type*) [Fintype V] where
  adjacency : V → V → ℝ
  lambda : ℝ
  left : V → ℝ
  right : V → ℝ
  lambda_pos : 0 < lambda
  left_pos : ∀ v, 0 < left v
  right_pos : ∀ v, 0 < right v
  adjacency_nonneg : ∀ v w, 0 ≤ adjacency v w
  left_eigen : ∀ w, ∑ v, left v * adjacency v w = lambda * left w
  right_eigen : ∀ v, ∑ w, adjacency v w * right w = lambda * right v
  normalize : ∑ v, left v * right v = 1

/-- Parry state weights `π(v) = l_v r_v`. -/
def phi_m_parry_state_weight {V : Type*} [Fintype V] (D : phi_m_parry_data V) (v : V) : ℝ :=
  D.left v * D.right v

/-- Parry transition probabilities
`P(v,w) = A(v,w) r_w / (λ r_v)`. -/
noncomputable def phi_m_parry_transition {V : Type*} [Fintype V]
    (D : phi_m_parry_data V) (v w : V) : ℝ :=
  D.adjacency v w * D.right w / (D.lambda * D.right v)

/-- The Markov package underlying the Parry measure: nonnegative normalized state weights,
nonnegative row-stochastic transitions, and stationarity. -/
noncomputable def phi_m_parry_is_markov {V : Type*} [Fintype V] (D : phi_m_parry_data V) :
    Prop :=
  (∀ v, 0 ≤ phi_m_parry_state_weight D v) ∧
  (∑ v, phi_m_parry_state_weight D v = 1) ∧
  (∀ v w, 0 ≤ phi_m_parry_transition D v w) ∧
  (∀ v, ∑ w, phi_m_parry_transition D v w = 1) ∧
  (∀ w, ∑ v, phi_m_parry_state_weight D v * phi_m_parry_transition D v w =
    phi_m_parry_state_weight D w)

lemma phi_m_parry_transition_row_sum {V : Type*} [Fintype V] (D : phi_m_parry_data V) (v : V) :
    ∑ w, phi_m_parry_transition D v w = 1 := by
  have hdenom : D.lambda * D.right v ≠ 0 := by
    exact mul_ne_zero (ne_of_gt D.lambda_pos) (ne_of_gt (D.right_pos v))
  calc
    ∑ w, phi_m_parry_transition D v w
        = ∑ w, (D.adjacency v w * D.right w) / (D.lambda * D.right v) := by
            simp [phi_m_parry_transition]
    _ = (∑ w, D.adjacency v w * D.right w) / (D.lambda * D.right v) := by
          rw [Finset.sum_div]
    _ = (D.lambda * D.right v) / (D.lambda * D.right v) := by
          rw [D.right_eigen v]
    _ = 1 := div_self hdenom

lemma phi_m_parry_stationary {V : Type*} [Fintype V] (D : phi_m_parry_data V) (w : V) :
    ∑ v, phi_m_parry_state_weight D v * phi_m_parry_transition D v w =
      phi_m_parry_state_weight D w := by
  have hlambda : D.lambda ≠ 0 := ne_of_gt D.lambda_pos
  calc
    ∑ v, phi_m_parry_state_weight D v * phi_m_parry_transition D v w
        = ∑ v, D.left v * D.adjacency v w * D.right w / D.lambda := by
            apply Finset.sum_congr rfl
            intro v hv
            have hright : D.right v ≠ 0 := ne_of_gt (D.right_pos v)
            unfold phi_m_parry_state_weight phi_m_parry_transition
            field_simp [hlambda, hright]
    _ = ∑ v, (D.left v * D.adjacency v w) * (D.right w / D.lambda) := by
          apply Finset.sum_congr rfl
          intro v hv
          field_simp [hlambda]
    _ = (∑ v, D.left v * D.adjacency v w) * (D.right w / D.lambda) := by
          rw [← Finset.sum_mul]
    _ = (D.lambda * D.left w) * (D.right w / D.lambda) := by
          rw [D.left_eigen w]
    _ = D.left w * D.right w := by
          field_simp [hlambda]
    _ = phi_m_parry_state_weight D w := by
          rfl

/-- The Perron--Frobenius weights and transition matrix define the normalized stationary Markov
chain that underlies the Parry measure on the `Φ_m` cover shift.
    prop:Phi_m-parry -/
theorem paper_phi_m_parry {V : Type*} [Fintype V] (D : phi_m_parry_data V) :
    phi_m_parry_is_markov D := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact mul_nonneg (le_of_lt (D.left_pos v)) (le_of_lt (D.right_pos v))
  · simpa [phi_m_parry_state_weight] using D.normalize
  · intro v w
    exact div_nonneg
      (mul_nonneg (D.adjacency_nonneg v w) (le_of_lt (D.right_pos w)))
      (mul_nonneg (le_of_lt D.lambda_pos) (le_of_lt (D.right_pos v)))
  · intro v
    exact phi_m_parry_transition_row_sum D v
  · intro w
    exact phi_m_parry_stationary D w

end Omega.Folding
