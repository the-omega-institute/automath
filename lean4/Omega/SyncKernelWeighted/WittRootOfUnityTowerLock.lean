import Mathlib.Tactic
import Omega.SyncKernelWeighted.WittFrobeniusIteratedDescent

namespace Omega.SyncKernelWeighted

open Polynomial

noncomputable section

/-- The polynomial family obtained by repeatedly applying Frobenius to the single variable `X`. -/
def witt_root_of_unity_tower_lock_family (n : ℕ) : Polynomial ℤ :=
  (Polynomial.X : Polynomial ℤ) ^ n

lemma witt_root_of_unity_tower_lock_descent_step (p j : ℕ) (hj : 1 ≤ j) :
    PolyZModEq (p ^ j) (witt_root_of_unity_tower_lock_family (p ^ j))
      ((witt_root_of_unity_tower_lock_family (p ^ (j - 1))).comp (Polynomial.X ^ p))
        := by
  unfold witt_root_of_unity_tower_lock_family
  have hpow :
      (((Polynomial.X : Polynomial ℤ) ^ (p ^ (j - 1))).comp (Polynomial.X ^ p)) =
        (Polynomial.X : Polynomial ℤ) ^ (p ^ j) := by
    calc
      (((Polynomial.X : Polynomial ℤ) ^ (p ^ (j - 1))).comp (Polynomial.X ^ p))
          = (Polynomial.X : Polynomial ℤ) ^ ((p ^ (j - 1)) * p) := by
              simpa using X_pow_comp_X_pow (p ^ (j - 1)) p
      _ = (Polynomial.X : Polynomial ℤ) ^ (p ^ ((j - 1) + 1)) := by
            rw [Nat.pow_succ']
            simp [Nat.mul_comm]
      _ = (Polynomial.X : Polynomial ℤ) ^ (p ^ j) := by
            simp [Nat.sub_add_cancel hj]
  simpa [hpow] using polyZModEq_refl (p ^ j) ((Polynomial.X : Polynomial ℤ) ^ (p ^ j))

lemma witt_root_of_unity_tower_lock_eval_eq_one
    (p k : ℕ) (u : ℤ) (hu : u ^ p = 1) (hk : 1 ≤ k) :
    (witt_root_of_unity_tower_lock_family (p ^ k)).eval u = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  calc
    (witt_root_of_unity_tower_lock_family (p ^ (1 + n))).eval u = u ^ (p ^ (1 + n)) := by
      simp [witt_root_of_unity_tower_lock_family]
    _ = u ^ (p * p ^ n) := by
      congr 1
      rw [Nat.add_comm, Nat.pow_succ]
      simp [Nat.mul_comm]
    _ = (u ^ p) ^ (p ^ n) := by rw [pow_mul]
    _ = 1 := by simp [hu]

/-- Paper label: `cor:witt-root-of-unity-tower-lock`. The iterated Frobenius descent theorem
reduces the level-`p^k` polynomial to the stage-`ell - 1` polynomial pushed forward by
`X ↦ X^(p^(k-ell+1))` modulo `p^ell`; evaluating at a `p`-th root of unity then collapses every
Frobenius pushforward to `1`. -/
theorem paper_witt_root_of_unity_tower_lock
    (p k ell : ℕ) (hp : Nat.Prime p) (hell : 1 ≤ ell) (hke : ell ≤ k) (u : ℤ)
    (hu : u ^ p = 1) :
    PolyZModEq (p ^ ell) (witt_root_of_unity_tower_lock_family (p ^ k))
      ((witt_root_of_unity_tower_lock_family (p ^ (ell - 1))).comp
        (Polynomial.X ^ (p ^ (k - ell + 1)))) ∧
    (witt_root_of_unity_tower_lock_family (p ^ k)).eval u = 1 ∧
    ((witt_root_of_unity_tower_lock_family (p ^ (ell - 1))).comp
      (Polynomial.X ^ (p ^ (k - ell + 1)))).eval u = 1 := by
  have hdescent :=
    paper_witt_frobenius_iterated_descent p k ell hp hell hke
      witt_root_of_unity_tower_lock_family (by
        intro j hj
        exact witt_root_of_unity_tower_lock_descent_step p j hj)
  have hk : 1 ≤ k := le_trans hell hke
  have h_eval_top :
      (witt_root_of_unity_tower_lock_family (p ^ k)).eval u = 1 :=
    witt_root_of_unity_tower_lock_eval_eq_one p k u hu hk
  have hcollapse :
      ((witt_root_of_unity_tower_lock_family (p ^ (ell - 1))).comp
        (Polynomial.X ^ (p ^ (k - ell + 1)))) =
        witt_root_of_unity_tower_lock_family (p ^ k) := by
    unfold witt_root_of_unity_tower_lock_family
    calc
      (((Polynomial.X : Polynomial ℤ) ^ (p ^ (ell - 1))).comp (Polynomial.X ^ (p ^ (k - ell + 1))))
          = (Polynomial.X : Polynomial ℤ) ^ ((p ^ (ell - 1)) * (p ^ (k - ell + 1))) := by
              simpa using X_pow_comp_X_pow (p ^ (ell - 1)) (p ^ (k - ell + 1))
      _ = (Polynomial.X : Polynomial ℤ) ^ (p ^ ((ell - 1) + (k - ell + 1))) := by
            rw [← Nat.pow_add]
      _ = (Polynomial.X : Polynomial ℤ) ^ (p ^ k) := by
            have hs : (ell - 1) + (k - ell + 1) = k := by
              omega
            simp [hs]
  have h_eval_lock :
      ((witt_root_of_unity_tower_lock_family (p ^ (ell - 1))).comp
        (Polynomial.X ^ (p ^ (k - ell + 1)))).eval u = 1 := by
    simpa [hcollapse] using h_eval_top
  exact ⟨hdescent, h_eval_top, h_eval_lock⟩

end

end Omega.SyncKernelWeighted
