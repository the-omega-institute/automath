import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The finite scale-entropy curve attached to atom masses `m` and depths `δ`. -/
def xi_defect_entropy_scale_fingerprint_stieltjes_curve
    (κ : Nat) (m δ : Fin κ → ℝ) (t : ℝ) : ℝ :=
  ∑ j : Fin κ, m j * δ j / (t + 1 + δ j)

/-- The signed formal derivative of one Stieltjes atom.

This is the quantity corresponding to `(-1)^n d^n/dt^n` for
`mass * depth / (t + 1 + depth)`. -/
def xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom
    (mass depth : ℝ) : Nat → ℝ → ℝ
  | 0, t => mass * depth / (t + 1 + depth)
  | n + 1, t =>
      (n + 1 : ℝ) *
        xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom mass depth n t /
          (t + 1 + depth)

/-- The finite signed derivative curve obtained by summing the atom derivatives. -/
def xi_defect_entropy_scale_fingerprint_stieltjes_signed_derivative
    (κ : Nat) (m δ : Fin κ → ℝ) (n : Nat) (t : ℝ) : ℝ :=
  ∑ j : Fin κ, xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom (m j) (δ j) n t

/-- The closed finite Stieltjes moment appearing in the signed derivative formula. -/
def xi_defect_entropy_scale_fingerprint_stieltjes_moment
    (κ : Nat) (m δ : Fin κ → ℝ) (n : Nat) (t : ℝ) : ℝ :=
  (Nat.factorial n : ℝ) *
    ∑ j : Fin κ, m j * δ j / (t + 1 + δ j) ^ (n + 1)

lemma xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom_formula
    (mass depth : ℝ) (n : Nat) (t : ℝ) (hden : t + 1 + depth ≠ 0) :
    xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom mass depth n t =
      (Nat.factorial n : ℝ) * mass * depth / (t + 1 + depth) ^ (n + 1) := by
  induction n with
  | zero =>
      simp [xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom]
  | succ n ih =>
      rw [xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom, ih]
      rw [Nat.factorial_succ]
      field_simp [hden]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring_nf

lemma xi_defect_entropy_scale_fingerprint_stieltjes_derivative_formula
    (κ : Nat) (m δ : Fin κ → ℝ) (n : Nat) (t : ℝ)
    (hden : ∀ j : Fin κ, t + 1 + δ j ≠ 0) :
    xi_defect_entropy_scale_fingerprint_stieltjes_signed_derivative κ m δ n t =
      xi_defect_entropy_scale_fingerprint_stieltjes_moment κ m δ n t := by
  unfold xi_defect_entropy_scale_fingerprint_stieltjes_signed_derivative
    xi_defect_entropy_scale_fingerprint_stieltjes_moment
  calc
    ∑ j : Fin κ, xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom (m j) (δ j) n t =
        ∑ j : Fin κ, (Nat.factorial n : ℝ) * m j * δ j /
          (t + 1 + δ j) ^ (n + 1) := by
      exact Finset.sum_congr rfl fun j _ =>
        xi_defect_entropy_scale_fingerprint_stieltjes_signed_atom_formula
          (m j) (δ j) n t (hden j)
    _ = (Nat.factorial n : ℝ) *
        ∑ j : Fin κ, m j * δ j / (t + 1 + δ j) ^ (n + 1) := by
      rw [Finset.mul_sum]
      congr
      ext j
      ring

lemma xi_defect_entropy_scale_fingerprint_stieltjes_moment_nonneg
    (κ : Nat) (m δ : Fin κ → ℝ) (hm : ∀ j, 0 ≤ m j) (hδ : ∀ j, 0 < δ j)
    (n : Nat) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ xi_defect_entropy_scale_fingerprint_stieltjes_moment κ m δ n t := by
  unfold xi_defect_entropy_scale_fingerprint_stieltjes_moment
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => by
    have hden_base : 0 ≤ t + 1 + δ j := by linarith [ht, hδ j]
    have hden : 0 ≤ (t + 1 + δ j) ^ (n + 1) := pow_nonneg hden_base _
    exact div_nonneg (mul_nonneg (hm j) (le_of_lt (hδ j))) hden)

/-- Concrete statement for the finite Stieltjes scale-entropy fingerprint. -/
def xi_defect_entropy_scale_fingerprint_stieltjes_statement
    (κ : Nat) (m δ : Fin κ → ℝ) : Prop :=
  (∀ j, 0 ≤ m j) →
    (∀ j, 0 < δ j) →
      ∀ n : Nat, ∀ t : ℝ, 0 ≤ t →
        xi_defect_entropy_scale_fingerprint_stieltjes_signed_derivative κ m δ n t =
            xi_defect_entropy_scale_fingerprint_stieltjes_moment κ m δ n t ∧
          0 ≤ xi_defect_entropy_scale_fingerprint_stieltjes_signed_derivative κ m δ n t

/-- Paper label: `prop:xi-defect-entropy-scale-fingerprint-stieltjes`. -/
theorem paper_xi_defect_entropy_scale_fingerprint_stieltjes
    (κ : Nat) (m δ : Fin κ → ℝ) :
    xi_defect_entropy_scale_fingerprint_stieltjes_statement κ m δ := by
  intro hm hδ n t ht
  have hden : ∀ j : Fin κ, t + 1 + δ j ≠ 0 := by
    intro j
    exact ne_of_gt (by linarith [ht, hδ j])
  have hformula :=
    xi_defect_entropy_scale_fingerprint_stieltjes_derivative_formula κ m δ n t hden
  constructor
  · exact hformula
  · rw [hformula]
    exact xi_defect_entropy_scale_fingerprint_stieltjes_moment_nonneg κ m δ hm hδ n t ht

end

end Omega.Zeta
