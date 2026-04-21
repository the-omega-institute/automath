import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

/-- Concrete finite-depth data for the prime-register embedding/collapse statement. The Newton
evaluation lift uses the first `depth` register coordinates, while `cutoff < depth` records a
finite observation depth and `boxBound > 1` provides a nontrivial coefficient box. -/
structure ProfinitePrimeRegisterEmbeddingCollapseData where
  depth : ℕ
  cutoff : ℕ
  hcutoff : cutoff < depth
  boxBound : ℕ
  hbox : 1 < boxBound

namespace ProfinitePrimeRegisterEmbeddingCollapseData

/-- Newton basis evaluation at the `k`th prime-register node, with the register nodes encoded by
their indices. The diagonal value is positive, while values above the diagonal vanish. -/
def newtonEval (i k : ℕ) : ℕ :=
  Finset.prod (Finset.range i) (fun j => k - j)

/-- Evaluation lift on the first `depth` Newton coordinates. -/
def coeffAt (D : ProfinitePrimeRegisterEmbeddingCollapseData) (a : Fin D.depth → ℕ) (i : ℕ) : ℕ :=
  if hi : i < D.depth then a ⟨i, hi⟩ else 0

/-- Evaluation lift on the first `depth` Newton coordinates. -/
def registerLift (D : ProfinitePrimeRegisterEmbeddingCollapseData) (a : Fin D.depth → ℕ) :
    Fin D.depth → ℕ := fun k =>
  Finset.sum (Finset.range (k.1 + 1)) (fun i => D.coeffAt a i * newtonEval i k.1)

/-- Coefficient vectors inside the finite box `{0, ..., boxBound - 1}^depth`. -/
abbrev BoxVector (D : ProfinitePrimeRegisterEmbeddingCollapseData) := Fin D.depth → Fin D.boxBound

/-- The lift to all prime-register coordinates is injective. -/
def injectiveLift (D : ProfinitePrimeRegisterEmbeddingCollapseData) : Prop :=
  Function.Injective D.registerLift

/-- Truncation to the first `cutoff` observed registers. -/
def truncateLift (D : ProfinitePrimeRegisterEmbeddingCollapseData) (v : D.BoxVector) :
    Fin D.cutoff → ℕ := fun k =>
  D.registerLift (fun i => (v i : ℕ)) ⟨k.1, lt_trans k.2 D.hcutoff⟩

/-- Finite-depth collapse: two different box vectors become indistinguishable after truncating the
prime-register lift to the first `cutoff` coordinates. -/
def finiteDepthCollapse (D : ProfinitePrimeRegisterEmbeddingCollapseData) : Prop :=
  ∃ v w : D.BoxVector, v ≠ w ∧ D.truncateLift v = D.truncateLift w

lemma newtonEval_diag_pos (k : ℕ) : 0 < newtonEval k k := by
  unfold newtonEval
  refine Finset.prod_pos ?_
  intro j hj
  exact Nat.sub_pos_of_lt (Finset.mem_range.mp hj)

lemma newtonEval_zero_of_lt {i k : ℕ} (hk : k < i) : newtonEval i k = 0 := by
  classical
  unfold newtonEval
  have hmem : k ∈ Finset.range i := Finset.mem_range.mpr hk
  rw [← Finset.insert_erase hmem, Finset.prod_insert]
  · simp
  · simp

lemma registerLift_injective (D : ProfinitePrimeRegisterEmbeddingCollapseData) :
    D.injectiveLift := by
  intro a b hLift
  funext i
  have hcoeff :
      ∀ k (hkDepth : k < D.depth), a ⟨k, hkDepth⟩ = b ⟨k, hkDepth⟩ := by
    intro k hkDepth
    induction k using Nat.strong_induction_on with
    | h k ih =>
        have hk := congrArg (fun f => f ⟨k, hkDepth⟩) hLift
        simp [registerLift, coeffAt, hkDepth, Finset.sum_range_succ] at hk
        have hprefix :
            Finset.sum (Finset.range k)
                (fun x => if h : x < D.depth then a ⟨x, h⟩ * newtonEval x k else 0) =
              Finset.sum (Finset.range k)
                (fun x => if h : x < D.depth then b ⟨x, h⟩ * newtonEval x k else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hxk : x < k := Finset.mem_range.mp hx
          have hxDepth : x < D.depth := lt_trans hxk hkDepth
          simp [hxDepth, ih x hxk hxDepth]
        rw [hprefix] at hk
        rw [Nat.mul_comm (a ⟨k, hkDepth⟩), Nat.mul_comm (b ⟨k, hkDepth⟩)] at hk
        have hk' := Nat.add_left_cancel hk
        exact Nat.eq_of_mul_eq_mul_left (newtonEval_diag_pos k) hk'
  cases i with
  | mk val isLt =>
      simpa using hcoeff val isLt

lemma finiteDepthCollapse_witness (D : ProfinitePrimeRegisterEmbeddingCollapseData) :
    D.finiteDepthCollapse := by
  classical
  let cutoffIndex : Fin D.depth := ⟨D.cutoff, D.hcutoff⟩
  have hbox0 : 0 < D.boxBound := lt_trans (by decide : 0 < 1) D.hbox
  let zeroCoeff : Fin D.boxBound := ⟨0, hbox0⟩
  let zeroVec : D.BoxVector := fun _ => zeroCoeff
  let oneCoeff : Fin D.boxBound := ⟨1, D.hbox⟩
  let spikeVec : D.BoxVector := fun i => if i = cutoffIndex then oneCoeff else zeroCoeff
  refine ⟨zeroVec, spikeVec, ?_, ?_⟩
  · intro hEq
    have := congrArg (fun f => f cutoffIndex) hEq
    simp [zeroVec, spikeVec, cutoffIndex, oneCoeff, zeroCoeff] at this
  · funext k
    have hk : k.1 < D.cutoff := k.2
    have hnotmem : D.cutoff ∉ Finset.range (k.1 + 1) := by
      simp [Nat.not_lt.mpr (Nat.succ_le_of_lt hk)]
    have hzero :
        D.registerLift (fun i => (spikeVec i : ℕ)) ⟨k.1, lt_trans k.2 D.hcutoff⟩ = 0 := by
      unfold registerLift
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxcutoff : x ≠ D.cutoff := by
        intro hEq
        exact hnotmem (hEq ▸ hx)
      simp [coeffAt, spikeVec, cutoffIndex, zeroCoeff, oneCoeff, hxcutoff]
    symm
    simpa [truncateLift, registerLift, coeffAt, zeroVec, zeroCoeff] using hzero

end ProfinitePrimeRegisterEmbeddingCollapseData

open ProfinitePrimeRegisterEmbeddingCollapseData

/-- Paper label: `prop:cdim-profinite-prime-register-embedding-collapse`. The finite Newton
evaluation lift is injective on the full prime-register depth, but any strict finite truncation
collapses two distinct vectors from the coefficient box. -/
theorem paper_cdim_profinite_prime_register_embedding_collapse
    (D : ProfinitePrimeRegisterEmbeddingCollapseData) :
    D.injectiveLift ∧ D.finiteDepthCollapse := by
  exact ⟨D.registerLift_injective, D.finiteDepthCollapse_witness⟩

end Omega.CircleDimension
