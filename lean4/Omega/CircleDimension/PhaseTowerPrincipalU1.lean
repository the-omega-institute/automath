import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

/-- Squared norm on the finite complex coordinate model for the unit sphere `S^{2n+1}`. -/
def phase_tower_principal_u1_total_weight {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  ∑ i, Complex.normSq (z i)

/-- The concrete unit sphere in `ℂ^(n+1)`, encoded by total squared norm `1`. -/
def phase_tower_principal_u1_unit_sphere (n : ℕ) :=
  {z : Fin (n + 1) → ℂ // phase_tower_principal_u1_total_weight z = 1}

/-- Global `U(1)` phase multiplication on coordinates. -/
def phase_tower_principal_u1_phase_action_vec {n : ℕ}
    (u : ℂ) (z : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  fun i => u * z i

/-- The `U(1)` action preserves the concrete unit sphere because `‖u‖ = 1`. -/
def phase_tower_principal_u1_phase_action {n : ℕ} (u : ℂ)
    (hu : Complex.normSq u = 1) (z : phase_tower_principal_u1_unit_sphere n) :
    phase_tower_principal_u1_unit_sphere n := by
  refine ⟨phase_tower_principal_u1_phase_action_vec u z.1, ?_⟩
  calc
    phase_tower_principal_u1_total_weight (phase_tower_principal_u1_phase_action_vec u z.1)
      = ∑ i, Complex.normSq u * Complex.normSq (z.1 i) := by
          simp [phase_tower_principal_u1_total_weight, phase_tower_principal_u1_phase_action_vec,
            Complex.normSq_mul]
    _ = Complex.normSq u * ∑ i, Complex.normSq (z.1 i) := by
          rw [Finset.mul_sum]
    _ = 1 * phase_tower_principal_u1_total_weight z.1 := by
          rw [hu]
          rfl
    _ = 1 := by
          rw [z.2]
          norm_num

/-- Two points define the same projective class exactly when they differ by a unit complex scalar. -/
def phase_tower_principal_u1_phase_equivalent {n : ℕ}
    (z w : phase_tower_principal_u1_unit_sphere n) : Prop :=
  ∃ u : ℂ, Complex.normSq u = 1 ∧ ∀ i, w.1 i = u * z.1 i

lemma phase_tower_principal_u1_phase_equivalent_refl {n : ℕ} :
    Reflexive (phase_tower_principal_u1_phase_equivalent (n := n)) := by
  intro z
  refine ⟨1, by simp, ?_⟩
  intro i
  simp

lemma phase_tower_principal_u1_phase_equivalent_symm {n : ℕ} :
    Symmetric (phase_tower_principal_u1_phase_equivalent (n := n)) := by
  intro z w h
  rcases h with ⟨u, hu, huw⟩
  have phase_tower_principal_u1_unit_ne_zero : u ≠ 0 := by
    intro hu0
    have : Complex.normSq u = 0 := by simp [hu0]
    rw [this] at hu
    norm_num at hu
  refine ⟨u⁻¹, by simpa [Complex.normSq_inv, hu], ?_⟩
  intro i
  have hcoord : w.1 i = u * z.1 i := huw i
  have hcalc : u⁻¹ * w.1 i = z.1 i := by
    rw [hcoord]
    field_simp [phase_tower_principal_u1_unit_ne_zero, mul_assoc]
  simpa [mul_comm] using hcalc.symm

lemma phase_tower_principal_u1_phase_equivalent_trans {n : ℕ} :
    Transitive (phase_tower_principal_u1_phase_equivalent (n := n)) := by
  intro z w x hzw hwx
  rcases hzw with ⟨u, hu, hzw⟩
  rcases hwx with ⟨v, hv, hvx⟩
  refine ⟨v * u, by simpa [Complex.normSq_mul, hu, hv], ?_⟩
  intro i
  calc
    x.1 i = v * w.1 i := hvx i
    _ = v * (u * z.1 i) := by rw [hzw i]
    _ = (v * u) * z.1 i := by simp [mul_assoc]

/-- Projectivization as the quotient by the global phase action. -/
def phase_tower_principal_u1_projective_setoid (n : ℕ) :
    Setoid (phase_tower_principal_u1_unit_sphere n) where
  r := phase_tower_principal_u1_phase_equivalent
  iseqv := ⟨@phase_tower_principal_u1_phase_equivalent_refl n,
    @phase_tower_principal_u1_phase_equivalent_symm n,
    @phase_tower_principal_u1_phase_equivalent_trans n⟩

/-- The quotient map from the unit sphere to projective space. -/
def phase_tower_principal_u1_projectivization (n : ℕ) :
    phase_tower_principal_u1_unit_sphere n →
      Quotient (phase_tower_principal_u1_projective_setoid n) :=
  Quotient.mk (phase_tower_principal_u1_projective_setoid n)

/-- The `n = 1` specialization is the Hopf fibration model. -/
abbrev phase_tower_principal_u1_hopf_fibration :=
  phase_tower_principal_u1_projectivization 1

lemma phase_tower_principal_u1_nonzero_coordinate {n : ℕ}
    (z : phase_tower_principal_u1_unit_sphere n) : ∃ i, z.1 i ≠ 0 := by
  by_contra hz
  have hall : ∀ i, z.1 i = 0 := by
    intro i
    by_contra hi
    exact hz ⟨i, hi⟩
  have hzero : phase_tower_principal_u1_total_weight z.1 = 0 := by
    simp [phase_tower_principal_u1_total_weight, hall]
  have : (1 : ℝ) = 0 := by rw [← z.2, hzero]
  norm_num at this

lemma phase_tower_principal_u1_free_action {n : ℕ} (u : ℂ)
    (z : phase_tower_principal_u1_unit_sphere n) (hu : Complex.normSq u = 1)
    (hfix : phase_tower_principal_u1_phase_action u hu z = z) : u = 1 := by
  rcases phase_tower_principal_u1_nonzero_coordinate z with ⟨i, hi⟩
  have hcoord : u * z.1 i = z.1 i := by
    simpa [phase_tower_principal_u1_phase_action, phase_tower_principal_u1_phase_action_vec] using
      congrArg (fun w : phase_tower_principal_u1_unit_sphere n => w.1 i) hfix
  have hcoord' : u * z.1 i = 1 * z.1 i := by simpa using hcoord
  exact mul_right_cancel₀ hi hcoord'

lemma phase_tower_principal_u1_projectivization_fiber_iff {n : ℕ}
    (z w : phase_tower_principal_u1_unit_sphere n) :
    phase_tower_principal_u1_projectivization n z =
      phase_tower_principal_u1_projectivization n w ↔
        phase_tower_principal_u1_phase_equivalent z w := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-- Paper-facing package for the global `U(1)` quotient model of the phase tower. -/
def phase_tower_principal_u1_statement : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    (∀ u : ℂ, ∀ z : phase_tower_principal_u1_unit_sphere n,
      ∀ hu : Complex.normSq u = 1,
        phase_tower_principal_u1_phase_action u hu z = z → u = 1) ∧
    (∀ z w : phase_tower_principal_u1_unit_sphere n,
      phase_tower_principal_u1_projectivization n z =
          phase_tower_principal_u1_projectivization n w ↔
        phase_tower_principal_u1_phase_equivalent z w)) ∧
  phase_tower_principal_u1_hopf_fibration = phase_tower_principal_u1_projectivization 1

/-- Paper label: `prop:phase-tower-principal-u1`. -/
theorem paper_phase_tower_principal_u1 : phase_tower_principal_u1_statement := by
  refine ⟨?_, rfl⟩
  intro n hn
  let _ := hn
  refine ⟨?_, ?_⟩
  · intro u z hu hfix
    exact phase_tower_principal_u1_free_action u z hu hfix
  · intro z w
    exact phase_tower_principal_u1_projectivization_fiber_iff z w

end Omega.CircleDimension
