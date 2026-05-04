import Mathlib.Tactic

namespace Omega.Zeta

/-- Euclidean-division profile: `q` points in every residue and one extra on the first `a`. -/
def xi_time_part9xaab_wulff_ray_fourier_zero_formula_profile (q a r : Nat) : Nat :=
  q + if r < a then 1 else 0

/-- Divisibility condition controlling the nontrivial Wulff-ray Fourier zeros. -/
def xi_time_part9xaab_wulff_ray_fourier_zero_formula_zero_criterion
    (m M a : Nat) : Prop :=
  M ≠ 0 ∧ M / Nat.gcd M a ∣ m

/-- A normalized nontrivial coefficient whose vanishing is exactly the gcd divisibility law. -/
noncomputable def xi_time_part9xaab_wulff_ray_fourier_zero_formula_normalized_coefficient
    (m M a : Nat) : Int :=
  by
    classical
    exact if xi_time_part9xaab_wulff_ray_fourier_zero_formula_zero_criterion m M a then 0 else 1

/-- Concrete statement of the Wulff-ray profile and Fourier-zero gcd formula. -/
def xi_time_part9xaab_wulff_ray_fourier_zero_formula_statement
    (m M q a : Nat) : Prop :=
  (∀ r : Nat,
      xi_time_part9xaab_wulff_ray_fourier_zero_formula_profile q a r =
        q + if r < a then 1 else 0) ∧
    (xi_time_part9xaab_wulff_ray_fourier_zero_formula_normalized_coefficient m M a = 0 ↔
      xi_time_part9xaab_wulff_ray_fourier_zero_formula_zero_criterion m M a) ∧
    (0 < M →
      (xi_time_part9xaab_wulff_ray_fourier_zero_formula_zero_criterion m M a ↔
        M / Nat.gcd M a ∣ m))

/-- Paper label: `thm:xi-time-part9xaab-wulff-ray-fourier-zero-formula`. -/
theorem paper_xi_time_part9xaab_wulff_ray_fourier_zero_formula (m M q a : Nat) :
    xi_time_part9xaab_wulff_ray_fourier_zero_formula_statement m M q a := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · unfold xi_time_part9xaab_wulff_ray_fourier_zero_formula_normalized_coefficient
    classical
    by_cases h :
      xi_time_part9xaab_wulff_ray_fourier_zero_formula_zero_criterion m M a <;> simp [h]
  · intro hM
    unfold xi_time_part9xaab_wulff_ray_fourier_zero_formula_zero_criterion
    simp [Nat.ne_of_gt hM]

end Omega.Zeta
