import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A single `p`-power cyclic block with a scalar weight. -/
structure CyclicPBlock where
  exponent : ℕ
  scalar : ℤ

/-- A chosen `p`-th root used to define Verschiebung on a cyclic block. -/
structure RootedCyclicPBlock (p : ℕ) where
  base : CyclicPBlock
  liftScalar : ℤ
  lift_spec : liftScalar ^ p = base.scalar

/-- The length of a `p`-power cyclic block. -/
def blockLength (p : ℕ) (B : CyclicPBlock) : ℕ :=
  p ^ B.exponent

/-- The explicit trace formula for powers of a cyclic block. -/
def blockTracePower (p : ℕ) (B : CyclicPBlock) (n : ℕ) : ℤ :=
  if blockLength p B ∣ n then (blockLength p B : ℤ) * B.scalar ^ n else 0

/-- Frobenius lowers the `p`-power length by one and replicates the block `p` times. -/
def frobeniusBlock (p : ℕ) (B : CyclicPBlock) : List CyclicPBlock :=
  match B.exponent with
  | 0 => [{ exponent := 0, scalar := B.scalar ^ p }]
  | k + 1 => List.replicate p { exponent := k, scalar := B.scalar ^ p }

/-- Verschiebung raises the `p`-power length by one using a chosen `p`-th root. -/
def verschiebungBlock {p : ℕ} (B : RootedCyclicPBlock p) : CyclicPBlock :=
  { exponent := B.base.exponent + 1, scalar := B.liftScalar }

/-- Frobenius on a finite direct sum of cyclic blocks. -/
def frobeniusSum (p : ℕ) (L : List CyclicPBlock) : List CyclicPBlock :=
  L.flatMap (frobeniusBlock p)

/-- Verschiebung on a finite family of rooted cyclic blocks. -/
def verschiebungSum {p : ℕ} (L : List (RootedCyclicPBlock p)) : List CyclicPBlock :=
  L.map verschiebungBlock

/-- The explicit `p`-fold direct sum of the base blocks. -/
def baseReplicateSum (p : ℕ) (L : List (RootedCyclicPBlock p)) : List CyclicPBlock :=
  L.flatMap fun B => List.replicate p B.base

/-- Trace on a finite direct sum is the sum of the block traces. -/
def directSumTrace (p : ℕ) : List CyclicPBlock → ℕ → ℤ
  | [], _ => 0
  | B :: L, n => blockTracePower p B n + directSumTrace p L n

private theorem pow_succ_dvd_mul_iff (hp : 0 < p) (k n : ℕ) :
    p ^ (k + 1) ∣ p * n ↔ p ^ k ∣ n := by
  rw [pow_succ]
  constructor
  · intro h
    exact Nat.dvd_of_mul_dvd_mul_left hp (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h)
  · intro h
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using mul_dvd_mul_right h p

private theorem directSumTrace_append (p : ℕ) (L₁ L₂ : List CyclicPBlock) (n : ℕ) :
    directSumTrace p (L₁ ++ L₂) n = directSumTrace p L₁ n + directSumTrace p L₂ n := by
  induction L₁ with
  | nil => simp [directSumTrace]
  | cons B L ih =>
      simp [directSumTrace, ih, add_assoc]

private theorem directSumTrace_replicate (p m : ℕ) (B : CyclicPBlock) (n : ℕ) :
    directSumTrace p (List.replicate m B) n = (m : ℤ) * blockTracePower p B n := by
  induction m with
  | zero =>
      simp [directSumTrace]
  | succ m ih =>
      calc
        directSumTrace p (List.replicate (m + 1) B) n
            = blockTracePower p B n + directSumTrace p (List.replicate m B) n := by
                rw [List.replicate_succ, directSumTrace]
        _ = blockTracePower p B n + (m : ℤ) * blockTracePower p B n := by rw [ih]
        _ = ((m : ℤ) + 1) * blockTracePower p B n := by ring
        _ = ((m + 1 : ℕ) : ℤ) * blockTracePower p B n := by norm_num

private theorem blockTracePower_frobenius
    (p : ℕ) (hp : 0 < p) (B : CyclicPBlock) (n : ℕ) :
    directSumTrace p (frobeniusBlock p B) n = blockTracePower p B (p * n) := by
  cases B with
  | mk exponent scalar =>
      cases exponent with
      | zero =>
          simp [frobeniusBlock, directSumTrace, blockTracePower, blockLength, pow_mul, Nat.mul_comm,
            Nat.mul_left_comm, Nat.mul_assoc]
      | succ k =>
          by_cases hdiv : p ^ k ∣ n
          · have hdiv' : p ^ (k + 1) ∣ p * n := (pow_succ_dvd_mul_iff hp k n).2 hdiv
            have hpow :
                directSumTrace p (frobeniusBlock p { exponent := k + 1, scalar := scalar }) n =
                  (p : ℤ) * ((p ^ k : ℤ) * scalar ^ (p * n)) := by
              rw [frobeniusBlock, directSumTrace_replicate, blockTracePower]
              simp [blockLength, hdiv, pow_mul]
            calc
              directSumTrace p (frobeniusBlock p { exponent := k + 1, scalar := scalar }) n
                  = (p : ℤ) * ((p ^ k : ℤ) * scalar ^ (p * n)) := hpow
              _ = (p ^ (k + 1) : ℤ) * scalar ^ (p * n) := by
                    simp [pow_succ, Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm]
              _ = blockTracePower p { exponent := k + 1, scalar := scalar } (p * n) := by
                    rw [blockTracePower]
                    simp [blockLength, hdiv', pow_mul]
          · have hdiv' : ¬ p ^ (k + 1) ∣ p * n := by
              exact mt (pow_succ_dvd_mul_iff hp k n).1 hdiv
            calc
              directSumTrace p (frobeniusBlock p { exponent := k + 1, scalar := scalar }) n
                  = (p : ℤ) * 0 := by
                      rw [frobeniusBlock, directSumTrace_replicate, blockTracePower]
                      simp [blockLength, hdiv]
              _ = 0 := by simp
              _ = blockTracePower p { exponent := k + 1, scalar := scalar } (p * n) := by
                    rw [blockTracePower]
                    simp [blockLength, hdiv']

private theorem directSumTrace_frobenius
    (p : ℕ) (hp : 0 < p) (L : List CyclicPBlock) (n : ℕ) :
    directSumTrace p (frobeniusSum p L) n = directSumTrace p L (p * n) := by
  induction L with
  | nil =>
      simp [frobeniusSum, directSumTrace]
  | cons B L ih =>
      have ih' : directSumTrace p (List.flatMap (frobeniusBlock p) L) n = directSumTrace p L (p * n) := by
        simpa [frobeniusSum] using ih
      rw [frobeniusSum, List.flatMap_cons, directSumTrace_append, directSumTrace]
      rw [blockTracePower_frobenius p hp B n, ih']

private theorem frobenius_verschiebungBlock
    (p : ℕ) (B : RootedCyclicPBlock p) :
    frobeniusBlock p (verschiebungBlock B) = List.replicate p B.base := by
  cases B with
  | mk base liftScalar lift_spec =>
      cases base with
      | mk exponent scalar =>
          simp [frobeniusBlock, verschiebungBlock, lift_spec]

private theorem frobenius_verschiebungSum
    (p : ℕ) (L : List (RootedCyclicPBlock p)) :
    frobeniusSum p (verschiebungSum L) = baseReplicateSum p L := by
  induction L with
  | nil =>
      simp [frobeniusSum, verschiebungSum, baseReplicateSum]
  | cons B L ih =>
      have ih' : List.flatMap (frobeniusBlock p) (List.map verschiebungBlock L) =
          List.flatMap (fun B => List.replicate p B.base) L := by
        simpa [frobeniusSum, verschiebungSum, baseReplicateSum] using ih
      rw [verschiebungSum, List.map_cons, frobeniusSum, List.flatMap_cons, baseReplicateSum, List.flatMap_cons]
      rw [frobenius_verschiebungBlock p B, ih']

set_option maxHeartbeats 400000 in
/-- On single `p`-power cyclic blocks, Frobenius reproduces the trace of the `p`-th power and
Verschiebung followed by Frobenius becomes the `p`-fold direct sum. Extending blockwise gives the
same identities for finite direct sums.
    prop:cyclic-p-typical-frobenius-verschiebung -/
theorem paper_cyclic_p_typical_frobenius_verschiebung
    (p : ℕ) (hp : Nat.Prime p) (L : List CyclicPBlock) (R : List (RootedCyclicPBlock p)) :
    (∀ n : ℕ, directSumTrace p (frobeniusSum p L) n = directSumTrace p L (p * n)) ∧
      frobeniusSum p (verschiebungSum R) = baseReplicateSum p R := by
  refine ⟨?_, frobenius_verschiebungSum p R⟩
  intro n
  exact directSumTrace_frobenius p hp.pos L n

end Omega.Zeta
