import Mathlib.Tactic
import Omega.Zeta.BooleanTwoLayerCokerAndModmKernelCount

namespace Omega.Zeta

/-- The scalar obstruction left by the Boolean two-layer Smith reduction. -/
def xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolvable
    (m b0 : Nat) : Prop :=
  Nat.gcd 2 m ∣ b0

/-- The scalar fiber count predicted by the single non-unit Smith factor `2`. -/
def xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolutionCount
    (m b0 : Nat) : Nat :=
  if _ : Nat.gcd 2 m ∣ b0 then
    Nat.gcd 2 m
  else
    0

/-- Concrete package for the mod-`m` Boolean two-layer congruence law.  The Smith interface
specialized to `(a,b)=(2,1)` leaves one factor `2` and all other factors `1`; hence the kernel
and every solvable scalar fiber have size `gcd(2,m)`, with the odd/even alternatives made
explicit. -/
def xi_disjointness_boolean_congruence_solvability_gcd2m_statement
    (q m : Nat) : Prop :=
  booleanTwoLayerCokernelFactors 2 1 (2 ^ q - 2) =
      1 :: 2 :: List.replicate (2 ^ q - 2) 1 ∧
    booleanTwoLayerModKernelCount 2 1 (2 ^ q - 2) m = Nat.gcd 2 m ∧
    (∀ b0 : Nat,
      xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolvable m b0 ↔
        Nat.gcd 2 m ∣ b0) ∧
    (∀ b0 : Nat,
      Nat.gcd 2 m ∣ b0 →
        xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolutionCount m b0 =
          Nat.gcd 2 m) ∧
    ((¬ 2 ∣ m) →
      Nat.gcd 2 m = 1 ∧
        ∀ b0 : Nat,
          xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolutionCount m b0 = 1) ∧
    (2 ∣ m →
      Nat.gcd 2 m = 2 ∧
        ∀ b0 : Nat,
          xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolutionCount m b0 =
            if 2 ∣ b0 then 2 else 0)

/-- Paper label: `prop:xi-disjointness-boolean-congruence-solvability-gcd2m`. -/
theorem paper_xi_disjointness_boolean_congruence_solvability_gcd2m
    (q m : Nat) (hq : 2 ≤ q) (hm : 1 ≤ m) :
    xi_disjointness_boolean_congruence_solvability_gcd2m_statement q m := by
  let _ := hq
  let _ := hm
  have hsmith :=
    paper_xi_boolean_two_layer_coker_and_modm_kernel_count 2 1 q m
  have hone_pow : (1 : Nat) ^ (2 ^ q - 2) = 1 := by simp
  have hmod :
      booleanTwoLayerModKernelCount 2 1 (2 ^ q - 2) m = Nat.gcd 2 m := by
    calc
      booleanTwoLayerModKernelCount 2 1 (2 ^ q - 2) m =
          Nat.gcd m 1 * Nat.gcd m 2 * Nat.gcd m 1 ^ (2 ^ q - 2) := by
            simpa [Nat.gcd_comm] using hsmith.2
      _ = Nat.gcd 2 m := by
        simp [Nat.gcd_comm]
  refine ⟨?_, hmod, ?_, ?_, ?_, ?_⟩
  · simpa using hsmith.1
  · intro b0
    rfl
  · intro b0 hb0
    simp [xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolutionCount, hb0]
  · intro hodd
    have hgcd : Nat.gcd 2 m = 1 := by
      have hgpos : 0 < Nat.gcd 2 m := Nat.gcd_pos_of_pos_left m (by omega)
      have hgle : Nat.gcd 2 m ≤ 2 := Nat.gcd_le_left m (by omega : 0 < 2)
      interval_cases h : Nat.gcd 2 m
      · rfl
      · have hdiv : 2 ∣ m := by
          simpa [h] using Nat.gcd_dvd_right 2 m
        exfalso
        exact hodd hdiv
    refine ⟨hgcd, ?_⟩
    intro b0
    have hb0 : Nat.gcd 2 m ∣ b0 := by
      rw [hgcd]
      exact one_dvd b0
    simp [xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolutionCount, hgcd]
  · intro h2m
    have hgcd : Nat.gcd 2 m = 2 := by
      exact Nat.dvd_antisymm (Nat.gcd_dvd_left 2 m) (Nat.dvd_gcd (dvd_refl 2) h2m)
    refine ⟨hgcd, ?_⟩
    intro b0
    by_cases hb0 : 2 ∣ b0
    · have hsolvable : Nat.gcd 2 m ∣ b0 := by
        simpa [hgcd] using hb0
      simp [xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolutionCount, hgcd,
        hb0]
    · have hnot_solvable : ¬ Nat.gcd 2 m ∣ b0 := by
        simpa [hgcd] using hb0
      simp [xi_disjointness_boolean_congruence_solvability_gcd2m_scalarSolutionCount,
        hnot_solvable, hb0]

end Omega.Zeta
