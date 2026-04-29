import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The single-height margin at center `x0` and defect parameter `δ`. -/
noncomputable def xi_comoving_prefix_chebyshev_center_law_margin (δ γ x0 : ℝ) : ℝ :=
  4 * δ / ((γ - x0) ^ 2 + (1 + δ) ^ 2)

/-- The finite-cluster margin obtained from a height-dependent choice of admissible `δ`'s. -/
noncomputable def xi_comoving_prefix_chebyshev_center_law_assignment_margin
    (Γ : Finset ℝ) (hΓ : Γ.Nonempty) (Δ : ℝ → ℝ) (x0 : ℝ) : ℝ :=
  Γ.inf' hΓ (fun γ => xi_comoving_prefix_chebyshev_center_law_margin (Δ γ) γ x0)

lemma xi_comoving_prefix_chebyshev_center_law_margin_monotone
    {δ₁ δ₂ γ x0 : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₁₂ : δ₁ ≤ δ₂) (hδ₂ : δ₂ ≤ 1 / 2) :
    xi_comoving_prefix_chebyshev_center_law_margin δ₁ γ x0 ≤
      xi_comoving_prefix_chebyshev_center_law_margin δ₂ γ x0 := by
  unfold xi_comoving_prefix_chebyshev_center_law_margin
  have hδ₂_nonneg : 0 ≤ δ₂ := le_trans hδ₁ hδ₁₂
  have hden₁ : 0 < (γ - x0) ^ 2 + (1 + δ₁) ^ 2 := by
    have hsq : 0 < (1 + δ₁) ^ 2 := by
      apply sq_pos_of_pos
      nlinarith
    nlinarith [sq_nonneg (γ - x0), hsq]
  have hden₂ : 0 < (γ - x0) ^ 2 + (1 + δ₂) ^ 2 := by
    have hsq : 0 < (1 + δ₂) ^ 2 := by
      apply sq_pos_of_pos
      nlinarith
    nlinarith [sq_nonneg (γ - x0), hsq]
  refine (div_le_div_iff₀ hden₁ hden₂).2 ?_
  let A : ℝ := (γ - x0) ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hstep :
      0 ≤ (δ₂ - δ₁) * (A + 1 - δ₁ * δ₂) := by
    have hgap₁ : 0 ≤ δ₂ - δ₁ := by
      nlinarith
    have hgap₂ : 0 ≤ A + 1 - δ₁ * δ₂ := by
      have hprod : δ₁ * δ₂ ≤ (1 / 2 : ℝ) ^ 2 := by
        nlinarith
      nlinarith
    nlinarith
  dsimp [A] at hstep
  nlinarith [hstep]

lemma xi_comoving_prefix_chebyshev_center_law_margin_le_of_sq_le
    {δ r γ x0 : ℝ} (hδ : 0 < δ) (h : r ^ 2 ≤ (γ - x0) ^ 2) :
    xi_comoving_prefix_chebyshev_center_law_margin δ γ x0 ≤
      4 * δ / (r ^ 2 + (1 + δ) ^ 2) := by
  unfold xi_comoving_prefix_chebyshev_center_law_margin
  have hden₁ : 0 < (γ - x0) ^ 2 + (1 + δ) ^ 2 := by
    have hsq : 0 < (1 + δ) ^ 2 := by
      apply sq_pos_of_pos
      nlinarith
    nlinarith [sq_nonneg (γ - x0), hsq]
  have hden₂ : 0 < r ^ 2 + (1 + δ) ^ 2 := by
    have hsq : 0 < (1 + δ) ^ 2 := by
      apply sq_pos_of_pos
      nlinarith
    nlinarith [sq_nonneg r, hsq]
  refine (div_le_div_iff₀ hden₁ hden₂).2 ?_
  nlinarith

lemma xi_comoving_prefix_chebyshev_center_law_le_margin_of_sq_le
    {δ r γ x0 : ℝ} (hδ : 0 < δ) (h : (γ - x0) ^ 2 ≤ r ^ 2) :
    4 * δ / (r ^ 2 + (1 + δ) ^ 2) ≤
      xi_comoving_prefix_chebyshev_center_law_margin δ γ x0 := by
  unfold xi_comoving_prefix_chebyshev_center_law_margin
  have hden₁ : 0 < r ^ 2 + (1 + δ) ^ 2 := by
    have hsq : 0 < (1 + δ) ^ 2 := by
      apply sq_pos_of_pos
      nlinarith
    nlinarith [sq_nonneg r, hsq]
  have hden₂ : 0 < (γ - x0) ^ 2 + (1 + δ) ^ 2 := by
    have hsq : 0 < (1 + δ) ^ 2 := by
      apply sq_pos_of_pos
      nlinarith
    nlinarith [sq_nonneg (γ - x0), hsq]
  refine (div_le_div_iff₀ hden₁ hden₂).2 ?_
  nlinarith

lemma xi_comoving_prefix_chebyshev_center_law_margin_lt_of_sq_lt
    {δ r γ x0 : ℝ} (hδ : 0 < δ) (h : r ^ 2 < (γ - x0) ^ 2) :
    xi_comoving_prefix_chebyshev_center_law_margin δ γ x0 <
      4 * δ / (r ^ 2 + (1 + δ) ^ 2) := by
  unfold xi_comoving_prefix_chebyshev_center_law_margin
  have hden₁ : 0 < (γ - x0) ^ 2 + (1 + δ) ^ 2 := by
    have hsq : 0 < (1 + δ) ^ 2 := by
      apply sq_pos_of_pos
      nlinarith
    nlinarith [sq_nonneg (γ - x0), hsq]
  have hden₂ : 0 < r ^ 2 + (1 + δ) ^ 2 := by
    have hsq : 0 < (1 + δ) ^ 2 := by
      apply sq_pos_of_pos
      nlinarith
    nlinarith [sq_nonneg r, hsq]
  refine (div_lt_div_iff₀ hden₁ hden₂).2 ?_
  nlinarith

/-- Paper label: `prop:xi-comoving-prefix-chebyshev-center-law`.
For a finite height cluster with endpoints `a ≤ b`, the worst admissible margin is attained by the
smallest allowed defect `δ₀`, and the resulting finite-center problem has the unique Chebyshev
center `(a + b) / 2`. -/
theorem paper_xi_comoving_prefix_chebyshev_center_law
    (Γ : Finset ℝ) (hΓ : Γ.Nonempty) {a b δ₀ : ℝ}
    (ha : a ∈ Γ) (hb : b ∈ Γ)
    (hbounds : ∀ γ ∈ Γ, a ≤ γ ∧ γ ≤ b)
    (hδ₀ : 0 < δ₀) (hδ₀_half : δ₀ ≤ 1 / 2) :
    (∀ x0 Δ,
      (∀ γ ∈ Γ, δ₀ ≤ Δ γ ∧ Δ γ ≤ 1 / 2) →
        xi_comoving_prefix_chebyshev_center_law_assignment_margin Γ hΓ (fun _ => δ₀) x0 ≤
          xi_comoving_prefix_chebyshev_center_law_assignment_margin Γ hΓ Δ x0) ∧
      (∀ x0,
        xi_comoving_prefix_chebyshev_center_law_assignment_margin Γ hΓ (fun _ => δ₀) x0 ≤
          4 * δ₀ / (((b - a) / 2) ^ 2 + (1 + δ₀) ^ 2)) ∧
      xi_comoving_prefix_chebyshev_center_law_assignment_margin Γ hΓ (fun _ => δ₀) ((a + b) / 2) =
        4 * δ₀ / (((b - a) / 2) ^ 2 + (1 + δ₀) ^ 2) := by
  have hab : a ≤ b := (hbounds a ha).2
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro x0 Δ hΔ
    unfold xi_comoving_prefix_chebyshev_center_law_assignment_margin
    refine Finset.le_inf' (s := Γ) (H := hΓ)
      (f := fun γ => xi_comoving_prefix_chebyshev_center_law_margin (Δ γ) γ x0) ?_
    intro γ hγ
    have hinf :
        Γ.inf' hΓ (fun γ => xi_comoving_prefix_chebyshev_center_law_margin δ₀ γ x0) ≤
          xi_comoving_prefix_chebyshev_center_law_margin δ₀ γ x0 := by
      exact Finset.inf'_le (s := Γ)
        (f := fun γ => xi_comoving_prefix_chebyshev_center_law_margin δ₀ γ x0) hγ
    exact hinf.trans <|
      xi_comoving_prefix_chebyshev_center_law_margin_monotone
        (le_of_lt hδ₀) (hΔ γ hγ).1 (hΔ γ hγ).2
  · intro x0
    by_cases hx : x0 ≤ m
    · have hr_le : r ≤ b - x0 := by
        dsimp [m, r] at hx ⊢
        nlinarith
      have hsq : r ^ 2 ≤ (b - x0) ^ 2 := by
        nlinarith [hr_nonneg, hr_le]
      have hinf :
          xi_comoving_prefix_chebyshev_center_law_assignment_margin Γ hΓ (fun _ => δ₀) x0 ≤
            xi_comoving_prefix_chebyshev_center_law_margin δ₀ b x0 := by
        unfold xi_comoving_prefix_chebyshev_center_law_assignment_margin
        simpa using
          (Finset.inf'_le (s := Γ)
            (f := fun γ => xi_comoving_prefix_chebyshev_center_law_margin δ₀ γ x0) hb)
      exact hinf.trans <|
        xi_comoving_prefix_chebyshev_center_law_margin_le_of_sq_le hδ₀ (by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq)
    · have hx' : m ≤ x0 := le_of_not_ge hx
      have hr_le : r ≤ x0 - a := by
        dsimp [m, r] at hx' ⊢
        nlinarith
      have hsq : r ^ 2 ≤ (a - x0) ^ 2 := by
        nlinarith [hr_nonneg, hr_le]
      have hinf :
          xi_comoving_prefix_chebyshev_center_law_assignment_margin Γ hΓ (fun _ => δ₀) x0 ≤
            xi_comoving_prefix_chebyshev_center_law_margin δ₀ a x0 := by
        unfold xi_comoving_prefix_chebyshev_center_law_assignment_margin
        simpa using
          (Finset.inf'_le (s := Γ)
            (f := fun γ => xi_comoving_prefix_chebyshev_center_law_margin δ₀ γ x0) ha)
      exact hinf.trans <|
        xi_comoving_prefix_chebyshev_center_law_margin_le_of_sq_le hδ₀ (by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq)
  · apply le_antisymm
    · have hinf :
        xi_comoving_prefix_chebyshev_center_law_assignment_margin Γ hΓ (fun _ => δ₀) m ≤
          xi_comoving_prefix_chebyshev_center_law_margin δ₀ a m := by
        unfold xi_comoving_prefix_chebyshev_center_law_assignment_margin
        simpa [m] using
          (Finset.inf'_le (s := Γ)
            (f := fun γ => xi_comoving_prefix_chebyshev_center_law_margin δ₀ γ m) ha)
      have hsq : (a - m) ^ 2 = r ^ 2 := by
        dsimp [m, r]
        ring_nf
      calc
        xi_comoving_prefix_chebyshev_center_law_assignment_margin Γ hΓ (fun _ => δ₀) m
            ≤ xi_comoving_prefix_chebyshev_center_law_margin δ₀ a m := hinf
        _ = 4 * δ₀ / (r ^ 2 + (1 + δ₀) ^ 2) := by
          unfold xi_comoving_prefix_chebyshev_center_law_margin
          rw [hsq]
        _ = 4 * δ₀ / (((b - a) / 2) ^ 2 + (1 + δ₀) ^ 2) := by rfl
    · unfold xi_comoving_prefix_chebyshev_center_law_assignment_margin
      have hbound :
          4 * δ₀ / (r ^ 2 + (1 + δ₀) ^ 2) ≤
            Γ.inf' hΓ (fun γ => xi_comoving_prefix_chebyshev_center_law_margin δ₀ γ m) := by
        refine Finset.le_inf' (s := Γ) (H := hΓ)
          (f := fun γ => xi_comoving_prefix_chebyshev_center_law_margin δ₀ γ m) ?_
        intro γ hγ
        have hγa : a ≤ γ := (hbounds γ hγ).1
        have hγb : γ ≤ b := (hbounds γ hγ).2
        have hsq : (γ - m) ^ 2 ≤ r ^ 2 := by
          dsimp [m, r]
          nlinarith
        exact xi_comoving_prefix_chebyshev_center_law_le_margin_of_sq_le hδ₀ hsq
      simpa [r] using hbound

end Omega.Zeta
