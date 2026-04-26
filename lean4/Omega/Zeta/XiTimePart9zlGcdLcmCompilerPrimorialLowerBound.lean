import Mathlib.Tactic
import Omega.POM.CoprimeLedgerPrimorialOptimality
import Omega.Zeta.XiChainInteriorBooleanFlagClosedForm

namespace Omega.Zeta

open Finset

/-- Paper-facing formulation of the chain-interior primorial lower bound. For `n = 0` the
statement is trivial; for `n > 0`, any injective `gcd`/`lcm` compiler on the `n`-point chain
interior lattice sends the top element to an integer at least as large as the product of the first
`n - 1` primes. -/
def xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_statement (n : Nat) : Prop :=
  if hn : 0 < n then
    ∀ η : Finset (Fin n) → ℕ,
      Function.Injective η →
      (∀ F : Finset (Fin n), (⟨0, hn⟩ : Fin n) ∈ F → 1 ≤ η F) →
      (∀ F G : Finset (Fin n),
        (⟨0, hn⟩ : Fin n) ∈ F →
          (⟨0, hn⟩ : Fin n) ∈ G →
            η (F ∩ G) = Nat.gcd (η F) (η G) ∧
              η (F ∪ G) = Nat.lcm (η F) (η G)) →
      Omega.POM.firstPrimeProduct (n - 1) ≤ η Finset.univ
  else
    True

/-- Paper label: `thm:xi-time-part9zl-gcd-lcm-compiler-primorial-lower-bound`. Normalizing by the
bottom element reduces any injective `gcd`/`lcm` compiler on the chain interior lattice to a
family of pairwise coprime atom values above `1`; the existing primorial comparison then bounds
the top image below by the product of the first `n - 1` primes. -/
theorem paper_xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound (n : Nat) :
    xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_statement n := by
  classical
  by_cases hn : 0 < n
  · simp [xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_statement, hn]
    intro η hηinj hηpos hηgcdlcm
    let bottom : Fin n := ⟨0, hn⟩
    let bottomSet : Finset (Fin n) := {bottom}
    let topSet : Finset (Fin n) := Finset.univ
    let xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_atom_elem :
        Fin (n - 1) → Fin n := fun i => ⟨i.1 + 1, by omega⟩
    let atom : Fin (n - 1) → Finset (Fin n) := fun i =>
      insert bottom ({xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_atom_elem i} :
        Finset (Fin n))
    let q : Fin (n - 1) → ℕ := fun i => η (atom i) / η bottomSet
    let topNorm : ℕ := η topSet / η bottomSet
    have _ := paper_xi_chain_interior_boolean_flag_closed_form n
    have hηpos' : ∀ F : Finset (Fin n), bottom ∈ F → 1 ≤ η F := by
      intro F hF
      exact hηpos F (by simpa [bottom] using hF)
    have hηgcdlcm' :
        ∀ F G : Finset (Fin n),
          bottom ∈ F →
            bottom ∈ G →
              η (F ∩ G) = Nat.gcd (η F) (η G) ∧
                η (F ∪ G) = Nat.lcm (η F) (η G) := by
      intro F G hF hG
      exact hηgcdlcm F G (by simpa [bottom] using hF) (by simpa [bottom] using hG)
    have hbottom_pos : 0 < η bottomSet := by
      exact Nat.succ_le_iff.mp (hηpos' bottomSet (by simp [bottomSet]))
    have hbottom_dvd :
        ∀ {F : Finset (Fin n)}, bottom ∈ F → η bottomSet ∣ η F := by
      intro F hF
      have hEq := (hηgcdlcm' bottomSet F (by simp [bottomSet]) hF).1
      exact Nat.gcd_eq_left_iff_dvd.mp (by simpa [bottomSet, hF] using hEq.symm)
    have hatom_elem_ne_bottom :
        ∀ i : Fin (n - 1),
          xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_atom_elem i ≠ bottom := by
      intro i h
      have hval := congrArg Fin.val h
      exact Nat.succ_ne_zero i.1 hval
    have hatom_ne_bottom : ∀ i : Fin (n - 1), atom i ≠ bottomSet := by
      intro i hEq
      have hs :
          xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_atom_elem i ∈ bottomSet := by
        rw [← hEq]
        simp [atom]
      simp [bottomSet, hatom_elem_ne_bottom i] at hs
    have hatom_dvd_top : ∀ i : Fin (n - 1), η (atom i) ∣ η topSet := by
      intro i
      have hEq := (hηgcdlcm' (atom i) topSet (by simp [atom]) (by simp [topSet])).1
      exact Nat.gcd_eq_left_iff_dvd.mp (by simpa [topSet] using hEq.symm)
    have hq_mul : ∀ i : Fin (n - 1), η (atom i) = η bottomSet * q i := by
      intro i
      exact (Nat.mul_div_cancel' (hbottom_dvd (by simp [atom]))).symm
    have htop_mul : η topSet = η bottomSet * topNorm := by
      exact (Nat.mul_div_cancel' (hbottom_dvd (by simp [topSet]))).symm
    have hq_two_le : ∀ i : Fin (n - 1), 2 ≤ q i := by
      intro i
      have hAtomPos : 0 < η (atom i) := by
        exact Nat.succ_le_iff.mp (hηpos' (atom i) (by simp [atom]))
      have hq_pos : 0 < q i := by
        refine Nat.pos_of_ne_zero ?_
        intro hq0
        have hzero : η (atom i) = 0 := by simpa [q, hq0] using hq_mul i
        exact Nat.ne_of_gt hAtomPos hzero
      have hneq : q i ≠ 1 := by
        intro hq1
        have hsame : η (atom i) = η bottomSet := by simpa [hq1] using hq_mul i
        exact hatom_ne_bottom i (hηinj hsame)
      omega
    have hq_pairwise : Pairwise fun i j : Fin (n - 1) => Nat.Coprime (q i) (q j) := by
      intro i j hij
      have hEq := (hηgcdlcm' (atom i) (atom j) (by simp [atom]) (by simp [atom])).1
      have hatom_inter : atom i ∩ atom j = bottomSet := by
        have hatom_elem_ne :
            xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_atom_elem i ≠
              xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_atom_elem j := by
          intro h
          have hval : i.1 = j.1 := by
            have hval' := congrArg Fin.val h
            exact Nat.succ.inj hval'
          exact hij (Fin.ext hval)
        ext x
        constructor
        · intro hx
          rcases Finset.mem_inter.mp hx with ⟨hx₁, hx₂⟩
          have hx₁' :
              x = bottom ∨
                x = xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_atom_elem i := by
            simpa [atom] using hx₁
          have hx₂' :
              x = bottom ∨
                x = xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_atom_elem j := by
            simpa [atom] using hx₂
          rcases hx₁' with rfl | hxi
          · simp [bottomSet]
          rcases hx₂' with rfl | hxj
          · simp [bottomSet]
          exact False.elim (hatom_elem_ne (hxi.symm.trans hxj))
        · intro hx
          have hx' : x = bottom := by simpa [bottomSet] using hx
          simp [atom, hx']
      have hgcd :
          η bottomSet = Nat.gcd (η bottomSet * q i) (η bottomSet * q j) := by
        simpa [hatom_inter, hq_mul i, hq_mul j] using hEq
      have hgcd' : η bottomSet = η bottomSet * Nat.gcd (q i) (q j) := by
        simpa [Nat.gcd_mul_left] using hgcd
      have hone : Nat.gcd (q i) (q j) = 1 := by
        have hmul : η bottomSet * 1 = η bottomSet * Nat.gcd (q i) (q j) := by
          simpa [Nat.mul_comm] using hgcd'
        exact (Nat.eq_of_mul_eq_mul_left hbottom_pos hmul).symm
      exact Nat.coprime_iff_gcd_eq_one.mpr hone
    have hq_dvd_topNorm : ∀ i : Fin (n - 1), q i ∣ topNorm := by
      intro i
      have hmul : η bottomSet * q i ∣ η bottomSet * topNorm := by
        simpa [hq_mul i, htop_mul] using hatom_dvd_top i
      exact Nat.dvd_of_mul_dvd_mul_left hbottom_pos hmul
    have hledger_dvd_topNorm : Omega.POM.ledgerProduct q ∣ topNorm := by
      unfold Omega.POM.ledgerProduct
      have hprod : ∀ s : Finset (Fin (n - 1)), (∏ i ∈ s, q i) ∣ topNorm := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simp
        · intro a s ha hs
          have hqa : q a ∣ topNorm := hq_dvd_topNorm a
          have hcop : Nat.Coprime (q a) (∏ b ∈ s, q b) := by
            rw [Nat.coprime_prod_right_iff]
            intro b hb
            have hab : a ≠ b := by
              intro hab
              exact ha (hab ▸ hb)
            exact hq_pairwise hab
          simpa [Finset.prod_insert, ha] using Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hqa hs
      simpa using hprod (Finset.univ : Finset (Fin (n - 1)))
    have hprimorial : Omega.POM.firstPrimeProduct (n - 1) ≤ Omega.POM.ledgerProduct q := by
      exact (Omega.POM.paper_pom_coprime_ledger_primorial_optimality
        (n - 1) 0 q hq_two_le hq_pairwise).2.1
    have htopNorm_pos : 0 < topNorm := by
      refine Nat.pos_of_ne_zero ?_
      intro hzero
      have htopPos : 0 < η topSet := by
        exact Nat.succ_le_iff.mp (hηpos' topSet (by simp [topSet]))
      have htopZero : η topSet = 0 := by simpa [topNorm, hzero] using htop_mul
      exact Nat.ne_of_gt htopPos htopZero
    have htopNorm_ge : Omega.POM.firstPrimeProduct (n - 1) ≤ topNorm :=
      le_trans hprimorial (Nat.le_of_dvd htopNorm_pos hledger_dvd_topNorm)
    calc
      Omega.POM.firstPrimeProduct (n - 1) ≤ topNorm := htopNorm_ge
      _ ≤ η topSet := by
        rw [htop_mul]
        simpa [Nat.mul_comm] using Nat.le_mul_of_pos_left topNorm hbottom_pos
      _ = η Finset.univ := rfl
  · simp [xi_time_part9zl_gcd_lcm_compiler_primorial_lower_bound_statement, hn]

end Omega.Zeta
