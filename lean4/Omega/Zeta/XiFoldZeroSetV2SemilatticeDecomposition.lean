import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Omega.Folding.FoldZeroCosetV2IntersectionRigidity
import Omega.Folding.FoldZeroDyadicTowerDisjointFibonacciCosets
import Omega.Folding.ZeroCosetUnion

namespace Omega.Zeta

open Omega.Folding

/-- The Fibonacci gcd-label attached to the `j`-th singleton zero spectrum. -/
def xi_fold_zero_set_v2_semilattice_decomposition_g (m j : ℕ) : ℕ :=
  Nat.gcd (Nat.fib (j + 1)) (Nat.fib (m + 2))

/-- The `v₂`-layer membership condition for the indexed zero-coset family. -/
def xi_fold_zero_set_v2_semilattice_decomposition_layer (m r j : ℕ) : Prop :=
  j ∈ Finset.range m ∧
    xi_fold_zero_set_v2_semilattice_decomposition_g m j ∣ Nat.fib (m + 2) / 2 ∧
    Nat.factorization (xi_fold_zero_set_v2_semilattice_decomposition_g m j) 2 = r

/-- Concrete semilattice package for the indexed Fibonacci zero-coset family: the fold-zero set is
the union of the singleton spectra with Fibonacci gcd labels; the positive labels are partitioned
by their `v₂`-layer; within one layer the rigid odd-coset intersection specification is stable;
divisibility gives coset nesting; and the dyadic tower contributes the half-index Fibonacci lower
bound on the sixfold subsequence. -/
def xi_fold_zero_set_v2_semilattice_decomposition_statement (m : ℕ) : Prop :=
  let M := Nat.fib (m + 2)
  foldFiberConvolutionKernelZeroSet M (Finset.range m) =
      (Finset.range m).biUnion (foldFiberSingletonZeroSet M) ∧
    (∀ j ∈ Finset.range m,
      xi_fold_zero_set_v2_semilattice_decomposition_g m j = Nat.fib (Nat.gcd (j + 1) (m + 2))) ∧
    (∀ j ∈ Finset.range m,
      xi_fold_zero_set_v2_semilattice_decomposition_g m j ∣ M / 2 →
        ∃! r, xi_fold_zero_set_v2_semilattice_decomposition_layer m r j) ∧
    (Even M →
      (∀ r j k,
        xi_fold_zero_set_v2_semilattice_decomposition_layer m r j →
          xi_fold_zero_set_v2_semilattice_decomposition_layer m r k →
            FoldZeroCosetV2IntersectionSpec M
              (xi_fold_zero_set_v2_semilattice_decomposition_g m j)
              (xi_fold_zero_set_v2_semilattice_decomposition_g m k)) ∧
        (∀ r j k,
          xi_fold_zero_set_v2_semilattice_decomposition_layer m r j →
            xi_fold_zero_set_v2_semilattice_decomposition_layer m r k →
              xi_fold_zero_set_v2_semilattice_decomposition_g m j ∣
                  xi_fold_zero_set_v2_semilattice_decomposition_g m k →
                foldZeroOddCoset M (xi_fold_zero_set_v2_semilattice_decomposition_g m j) ⊆
                  foldZeroOddCoset M (xi_fold_zero_set_v2_semilattice_decomposition_g m k))) ∧
    ((m + 2) % 6 = 0 → Nat.fib ((m + 2) / 2) ≤ (foldZeroFrequencyUnion m).card)

private lemma xi_fold_zero_set_v2_semilattice_decomposition_odd_quotient_of_same_v2
    {g h : ℕ} (hg : 0 < g) (hh : 0 < h) (hgh : g ∣ h)
    (hfac : Nat.factorization g 2 = Nat.factorization h 2) :
    Odd (h / g) := by
  rcases hgh with ⟨q, rfl⟩
  have hq_ne_zero : q ≠ 0 := by
    intro hq0
    subst hq0
    simp at hh
  have hmul2 :
      Nat.factorization (g * q) 2 = Nat.factorization g 2 + Nat.factorization q 2 := by
    simpa [Finsupp.add_apply] using
      congrArg (fun f => f 2) (Nat.factorization_mul hg.ne' hq_ne_zero)
  rw [← hfac] at hmul2
  have hqfac : Nat.factorization q 2 = 0 := by omega
  have hnotdvd : ¬ 2 ∣ q := by
    intro htwo
    have hpos :
        0 < Nat.factorization q 2 := Nat.prime_two.factorization_pos_of_dvd hq_ne_zero htwo
    omega
  have hoddq : Odd q := Nat.not_even_iff_odd.mp fun hEven => hnotdvd hEven.two_dvd
  simpa [Nat.mul_div_right q hg] using hoddq

private lemma xi_fold_zero_set_v2_semilattice_decomposition_subset_of_dvd_odd
    {M g h : ℕ} (hg : 0 < g) (hh : 0 < h) (hhdiv : h ∣ M / 2) (hgh : g ∣ h)
    (hodd : Odd (h / g)) :
    foldZeroOddCoset M g ⊆ foldZeroOddCoset M h := by
  rcases hgh with ⟨d, rfl⟩
  rcases hodd with ⟨m, hm⟩
  have hd : d = 2 * m + 1 := by
    simpa [Nat.mul_div_right _ hg] using hm
  rcases hhdiv with ⟨q, hq⟩
  intro x hx
  rw [foldZeroOddCoset] at hx ⊢
  rcases Finset.mem_image.mp hx with ⟨k, hk, hkx⟩
  refine Finset.mem_image.mpr ?_
  refine ⟨m + k * (2 * m + 1), ?_, ?_⟩
  · have hk' : k < g := by simpa [hd] using hk
    have hm_lt : m < 2 * m + 1 := by omega
    simpa [hd] using
      (calc
        m + k * (2 * m + 1) < (2 * m + 1) + k * (2 * m + 1) := by gcongr
        _ = (k + 1) * (2 * m + 1) := by ring
        _ ≤ g * (2 * m + 1) := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hk')
        _ = g * d := by rw [hd])
  · have hhalf_h : M / 2 / (g * d) = q := by
      rw [hq]
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using Nat.mul_div_right q hh
    have hhalf_g : M / 2 / g = d * q := by
      rw [hq]
      calc
        (g * d * q) / g = (g * (d * q)) / g := by ring
        _ = d * q := Nat.mul_div_right (d * q) hg
    rw [← hkx, hhalf_h, hhalf_g, hd]
    ring

/-- Paper label: `cor:xi-fold-zero-set-v2-semilattice-decomposition`. -/
theorem paper_xi_fold_zero_set_v2_semilattice_decomposition (m : ℕ) :
    xi_fold_zero_set_v2_semilattice_decomposition_statement m := by
  dsimp [xi_fold_zero_set_v2_semilattice_decomposition_statement]
  let M := Nat.fib (m + 2)
  have hunion := Omega.Folding.paper_fold_zero_coset_union m
  refine ⟨hunion.1, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simpa [xi_fold_zero_set_v2_semilattice_decomposition_g] using hunion.2 j hj
  · intro j hj hdiv
    refine ⟨Nat.factorization (xi_fold_zero_set_v2_semilattice_decomposition_g m j) 2, ?_, ?_⟩
    · exact ⟨hj, hdiv, rfl⟩
    · intro r hr
      exact hr.2.2.symm
  · intro hEven
    refine ⟨?_, ?_⟩
    · intro r j k hj hk
      exact Omega.Folding.paper_xi_fold_zero_coset_v2_intersection_rigidity
        M
        (xi_fold_zero_set_v2_semilattice_decomposition_g m j)
        (xi_fold_zero_set_v2_semilattice_decomposition_g m k)
        hEven hj.2.1 hk.2.1
    · intro r j k hj hk hdiv
      have hjpos :
          0 < xi_fold_zero_set_v2_semilattice_decomposition_g m j := by
        unfold xi_fold_zero_set_v2_semilattice_decomposition_g
        exact Nat.gcd_pos_of_pos_left _ (Nat.fib_pos.mpr (by omega))
      have hkpos :
          0 < xi_fold_zero_set_v2_semilattice_decomposition_g m k := by
        unfold xi_fold_zero_set_v2_semilattice_decomposition_g
        exact Nat.gcd_pos_of_pos_left _ (Nat.fib_pos.mpr (by omega))
      have hodd :
          Odd
            (xi_fold_zero_set_v2_semilattice_decomposition_g m k /
              xi_fold_zero_set_v2_semilattice_decomposition_g m j) :=
        xi_fold_zero_set_v2_semilattice_decomposition_odd_quotient_of_same_v2
          hjpos hkpos hdiv (by rw [hj.2.2, hk.2.2])
      exact xi_fold_zero_set_v2_semilattice_decomposition_subset_of_dvd_odd
        hjpos hkpos hk.2.1 hdiv hodd
  · intro hm6
    exact (Omega.Folding.paper_xi_fold_zero_dyadic_tower_disjoint_fibonacci_cosets m hm6).2

end Omega.Zeta
