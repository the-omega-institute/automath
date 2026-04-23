import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter

noncomputable section

structure conclusion_prime_register_crossresolution_rigidity_attractor_data where
  conclusion_prime_register_crossresolution_rigidity_attractor_baseAction : ℕ → ℝ
  conclusion_prime_register_crossresolution_rigidity_attractor_liftedAction : ℕ → ℝ
  conclusion_prime_register_crossresolution_rigidity_attractor_layer_agree :
    ∀ n : ℕ,
      conclusion_prime_register_crossresolution_rigidity_attractor_liftedAction n =
        conclusion_prime_register_crossresolution_rigidity_attractor_baseAction n
  conclusion_prime_register_crossresolution_rigidity_attractor_B : ℝ
  conclusion_prime_register_crossresolution_rigidity_attractor_k : ℕ
  conclusion_prime_register_crossresolution_rigidity_attractor_x_g : ℝ
  conclusion_prime_register_crossresolution_rigidity_attractor_contraction :
    |conclusion_prime_register_crossresolution_rigidity_attractor_B ^
        conclusion_prime_register_crossresolution_rigidity_attractor_k| < 1

namespace conclusion_prime_register_crossresolution_rigidity_attractor_data

def conclusion_prime_register_crossresolution_rigidity_attractor_Psi
    (D : conclusion_prime_register_crossresolution_rigidity_attractor_data) (x : ℝ) : ℝ :=
  D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
      D.conclusion_prime_register_crossresolution_rigidity_attractor_k *
    (x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g) +
      D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g

def conclusion_prime_register_crossresolution_rigidity_attractor_iterate
    (D : conclusion_prime_register_crossresolution_rigidity_attractor_data) (n : ℕ) (x : ℝ) : ℝ :=
  D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
      (D.conclusion_prime_register_crossresolution_rigidity_attractor_k * n) *
    (x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g) +
      D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g

def conclusion_prime_register_crossresolution_rigidity_attractor_unique_extension
    (D : conclusion_prime_register_crossresolution_rigidity_attractor_data) : Prop :=
  D.conclusion_prime_register_crossresolution_rigidity_attractor_liftedAction =
    D.conclusion_prime_register_crossresolution_rigidity_attractor_baseAction

def conclusion_prime_register_crossresolution_rigidity_attractor_unique_fixed_point
    (D : conclusion_prime_register_crossresolution_rigidity_attractor_data) : Prop :=
  conclusion_prime_register_crossresolution_rigidity_attractor_Psi D
      D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g =
    D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g ∧
      ∀ x : ℝ,
        conclusion_prime_register_crossresolution_rigidity_attractor_Psi D x = x →
          x = D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g

def conclusion_prime_register_crossresolution_rigidity_attractor_global_attractor
    (D : conclusion_prime_register_crossresolution_rigidity_attractor_data) : Prop :=
  ∀ x : ℝ,
    Tendsto
      (fun n : ℕ => conclusion_prime_register_crossresolution_rigidity_attractor_iterate D n x)
      atTop (nhds D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g)

lemma conclusion_prime_register_crossresolution_rigidity_attractor_pow_ne_one
    (D : conclusion_prime_register_crossresolution_rigidity_attractor_data) :
    D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
        D.conclusion_prime_register_crossresolution_rigidity_attractor_k ≠
      1 := by
  intro hpow
  have hone :
      |D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
          D.conclusion_prime_register_crossresolution_rigidity_attractor_k| =
        (1 : ℝ) := by
    simp [hpow]
  have hnot :
      ¬ |D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
            D.conclusion_prime_register_crossresolution_rigidity_attractor_k| <
          1 := by
    rw [hone]
    linarith
  exact hnot D.conclusion_prime_register_crossresolution_rigidity_attractor_contraction

lemma conclusion_prime_register_crossresolution_rigidity_attractor_iterate_eq_geometric
    (D : conclusion_prime_register_crossresolution_rigidity_attractor_data) (n : ℕ) (x : ℝ) :
    conclusion_prime_register_crossresolution_rigidity_attractor_iterate D n x =
      (D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
          D.conclusion_prime_register_crossresolution_rigidity_attractor_k) ^
        n *
          (x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g) +
        D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g := by
  simp [conclusion_prime_register_crossresolution_rigidity_attractor_iterate, pow_mul]

end conclusion_prime_register_crossresolution_rigidity_attractor_data

open conclusion_prime_register_crossresolution_rigidity_attractor_data

/-- Paper label: `thm:conclusion-prime-register-crossresolution-rigidity-attractor`. -/
theorem paper_conclusion_prime_register_crossresolution_rigidity_attractor
    (D : conclusion_prime_register_crossresolution_rigidity_attractor_data) :
    D.conclusion_prime_register_crossresolution_rigidity_attractor_unique_extension ∧
      D.conclusion_prime_register_crossresolution_rigidity_attractor_unique_fixed_point ∧
        D.conclusion_prime_register_crossresolution_rigidity_attractor_global_attractor := by
  refine ⟨?_, ?_, ?_⟩
  · funext n
    exact D.conclusion_prime_register_crossresolution_rigidity_attractor_layer_agree n
  · refine ⟨by
      simp [conclusion_prime_register_crossresolution_rigidity_attractor_Psi], ?_⟩
    intro x hx
    have hmul :
        (D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
              D.conclusion_prime_register_crossresolution_rigidity_attractor_k -
            1) *
          (x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g) =
          0 := by
      dsimp [conclusion_prime_register_crossresolution_rigidity_attractor_Psi] at hx
      linarith
    have hcoef :
        D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
              D.conclusion_prime_register_crossresolution_rigidity_attractor_k -
            1 ≠
          0 := by
      exact sub_ne_zero.mpr
        (conclusion_prime_register_crossresolution_rigidity_attractor_pow_ne_one D)
    have hxg : x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hcoef
    linarith
  · intro x
    have hpow :
        Tendsto
          (fun n : ℕ =>
            (D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
                D.conclusion_prime_register_crossresolution_rigidity_attractor_k) ^
              n)
          atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        D.conclusion_prime_register_crossresolution_rigidity_attractor_contraction
    have hmul :
        Tendsto
          (fun n : ℕ =>
            (x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g) *
              (D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
                  D.conclusion_prime_register_crossresolution_rigidity_attractor_k) ^
                n)
          atTop
          (nhds
            ((x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g) * 0)) :=
      hpow.const_mul (x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g)
    have hadd :
        Tendsto
          (fun n : ℕ =>
            (x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g) *
                (D.conclusion_prime_register_crossresolution_rigidity_attractor_B ^
                    D.conclusion_prime_register_crossresolution_rigidity_attractor_k) ^
                  n +
              D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g)
          atTop
          (nhds
            ((x - D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g) * 0 +
              D.conclusion_prime_register_crossresolution_rigidity_attractor_x_g)) :=
      hmul.add tendsto_const_nhds
    simpa [conclusion_prime_register_crossresolution_rigidity_attractor_iterate_eq_geometric,
      mul_comm, mul_left_comm, mul_assoc]
      using hadd

end

end Omega.Conclusion
