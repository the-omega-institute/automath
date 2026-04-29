import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Permutation
import Omega.Zeta.CyclicDet

namespace Omega.Zeta

open Equiv Matrix

private lemma cyclic_block_tensor_gcd_lcm_cyclicPerm_eq_finRotate_permMatrix (n : ℕ) :
    cyclicPerm n = (finRotate n).permMatrix ℤ := by
  cases n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n =>
      ext i j
      have hcycle : cyclicPerm.Fin.cycle (n + 1) i = i + 1 := by
        ext
        simp [cyclicPerm.Fin.cycle, Fin.add_def]
      simp [cyclicPerm, Equiv.Perm.permMatrix, finRotate_succ_apply, hcycle, eq_comm]

private lemma cyclic_block_tensor_gcd_lcm_permMatrix_pow {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (m : ℕ) : σ.permMatrix ℤ ^ m = (σ ^ m).permMatrix ℤ := by
  induction m with
  | zero =>
      simp
  | succ m hm =>
      rw [pow_succ, hm, ← Matrix.permMatrix_mul, pow_succ']

private lemma cyclic_block_tensor_gcd_lcm_finRotate_pow_lcm (n n' : ℕ) :
    (finRotate n : Equiv.Perm (Fin n)) ^ Nat.lcm n n' = 1 := by
  cases n with
  | zero =>
      simp
  | succ n =>
      cases n with
      | zero =>
          rw [show (finRotate 1 : Equiv.Perm (Fin 1)) = 1 by
            rw [finRotate_one]
            rfl]
          exact one_pow (Nat.lcm 1 n')
      | succ n =>
          have hcycle : Equiv.Perm.IsCycle (finRotate (n + 2)) := isCycle_finRotate
          have horder : orderOf (finRotate (n + 2)) = n + 2 := by
            rw [hcycle.orderOf, support_finRotate, Finset.card_univ, Fintype.card_fin]
          rw [← orderOf_dvd_iff_pow_eq_one, horder]
          exact Nat.dvd_lcm_left (n + 2) n'

/-- Paper label: `prop:cyclic-block-tensor-gcd-lcm`. The common period of the two cyclic
permutation blocks is `Nat.lcm n n'`, and the arithmetic identity
`Nat.gcd n n' * Nat.lcm n n' = n * n'` records the decomposition into
`gcd(n,n')` synchronized cycles of length `lcm(n,n')`. -/
theorem paper_cyclic_block_tensor_gcd_lcm (n n' : ℕ) :
    cyclicPerm n ^ Nat.lcm n n' = 1 ∧
      cyclicPerm n' ^ Nat.lcm n n' = 1 ∧ Nat.gcd n n' * Nat.lcm n n' = n * n' := by
  have hpow_n : (finRotate n : Equiv.Perm (Fin n)) ^ Nat.lcm n n' = 1 :=
    cyclic_block_tensor_gcd_lcm_finRotate_pow_lcm n n'
  have hpow_n' : (finRotate n' : Equiv.Perm (Fin n')) ^ Nat.lcm n n' = 1 := by
    simpa [Nat.lcm_comm] using cyclic_block_tensor_gcd_lcm_finRotate_pow_lcm n' n
  refine ⟨?_, ?_⟩
  · rw [cyclic_block_tensor_gcd_lcm_cyclicPerm_eq_finRotate_permMatrix,
      cyclic_block_tensor_gcd_lcm_permMatrix_pow, hpow_n]
    simp
  · refine ⟨?_, Nat.gcd_mul_lcm n n'⟩
    rw [cyclic_block_tensor_gcd_lcm_cyclicPerm_eq_finRotate_permMatrix,
      cyclic_block_tensor_gcd_lcm_permMatrix_pow, hpow_n']
    simp

end Omega.Zeta
